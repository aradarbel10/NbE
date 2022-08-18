{-# LANGUAGE DerivingVia, PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}

import Data.List                 ( elemIndex, intercalate )
import Data.Bifunctor            (first, bimap)

import Control.Monad.Identity    ( Identity, when, liftM2 )
import Control.Monad.Trans.State ( StateT, get, put, runStateT )

import Text.Parsec               ( Parsec, (<|>), getState, many1, ParseError, runParser, modifyState, SourcePos, try, optional, oneOf, (<?>) )
import Text.Parsec.Token         ( makeTokenParser, GenTokenParser(identifier, parens, reserved, reservedOp), GenLanguageDef (..) )
import Text.Parsec.Expr          ( )
import Text.Parsec.Language      ( haskellStyle )

import System.IO                 (hFlush, stdout)
import Debug.Trace               (trace, traceShowId)



indexOf :: Eq a => [a] -> a -> Maybe Int
indexOf [] _ = Nothing
indexOf (x:xs) y = if x == y then Just 0 else (1+) <$> indexOf xs y

lookupIndex :: Eq a => [(a, b)] -> a -> Maybe (Int, b)
lookupIndex [] _ = Nothing
lookupIndex ((x, z):xs) y = if x == y then Just (0, z) else first (1+) <$> lookupIndex xs y


data MetaCtx = MetaCtx -- TODO
type ErrMsg = (String, SourcePos)
data EnvRec = EnvRec { fri :: Integer, mctx :: MetaCtx }
type EnvM a = StateT EnvRec (Either ErrMsg) a

runEnv :: EnvM a -> Either ErrMsg a
runEnv m = fst <$> runStateT m (EnvRec 0 MetaCtx)


fresh :: Name -> EnvM Name
fresh x = do
    curr <- get
    put $ curr {fri = fri curr + 1}
    return $ x ++ show (fri curr)

newMeta :: Name -> EnvM Trm
newMeta x = do
    x' <- fresh x
    return (Meta x')


type Name = String

newtype Idx     = Idx     {unIdx  :: Int} deriving (Show, Eq, Num) via Int
newtype Lvl     = Lvl     {unLvl  :: Int} deriving (Show, Eq, Num) via Int
type    Siz = Lvl

--- user-facing
type RTyp = Raw
data Raw = RLam Name Raw
         | RApp Raw Raw
         | RLet Name RTyp Raw Raw
         | RPi (Maybe Name) RTyp Raw
         | RAnn Raw RTyp
         | RUni
         | RHole
         | RVar Name
    deriving Show
--- core language
type Spine = [Name]
type Typ = Trm
data Trm = Lam Name Typ Trm     -- λn . e
         | App Trm Trm          -- (e1 e2)
         | Let Name Typ Trm Trm -- let n = e in e'
         | Pi Name Typ Trm      -- Π(x:A).Bx
         | Uni
         | Meta Name
         | Var Idx
--- semantic domain
type VTyp = Val
data Val = VLam Name VTyp (Val -> Val)
         | VPi Name VTyp (Val -> Val)
         | VUni
         | VNeu Neu
data Neu = NVar Lvl
         | NMeta Name
         | NApp Neu Val
      -- | NProj1 Neu
      -- | NProj2 Neu

pattern VVar :: Lvl -> Val
pattern VVar lvl = VNeu (NVar lvl)

pattern VApp :: Neu -> Val -> Val
pattern VApp neu val = VNeu (NApp neu val)

pattern VMeta :: Name -> Val
pattern VMeta n = VNeu (NMeta n)

{-# COMPLETE VLam, VPi, VUni, VNeu, VVar, VApp, VMeta #-}



type Env = [(Name, Val)]


{-
          ╔═String══════╗
          ║             ║
          ║       ╿     ║
          ╚═══════╪═════╝
                parse
          ╔═Raw═══╪═════╗
          ║       ↓     ║
          ║       ╿     ║
          ╚═══════╪═════╝
                 elab
                  │    
          ╔═Term══╪═════╗         ╔═Value════╗
          ║       ↓     ║         ║          ║
          ║             ║         ║          ║
     ╭────╫───╼    ╾────╫──eval───╫───►  ╾───╫────╮
  normal  ║╔═Normal════╗║         ║          ║   vApp
     ╰────╫╫──►    ◄───╫╫──quote──╫───╼  ◄───╫────╯
          ║╚═══════════╝║         ╚══════════╝
          ╚═════════════╝ 
-}




--- parsing
type Parser a = Parsec String () a

lexer :: GenTokenParser String u Identity
lexer = makeTokenParser $ haskellStyle
    { reservedNames = ["Type", "lam", "let", "in", "_"]
    , reservedOpNames = ["=", ".", ":", "->"]
    }

parse :: String -> Either ParseError Raw
parse = runParser parseTerm () ""


parseName :: Parser Name
parseName = identifier lexer

parseParam :: Parser (Maybe Name, RTyp)
parseParam = try (parens lexer (do
                    n <- (Just <$> parseName) <|> (reserved lexer "_" >> pure Nothing)
                    reservedOp lexer ":"
                    t <- parseTerm
                    return (n, t)))
             <|> ((Nothing,) <$> parseAtom)


parseLam :: Parser Raw
parseLam = do
    reserved lexer "lam"
    ns <- many1 parseName
    reservedOp lexer "."
    e <- parseTerm
    return $ foldr RLam e ns

parseLet :: Parser Raw
parseLet = do
    reserved lexer "let"
    n <- parseName
    reservedOp lexer ":"
    t <- parseTerm
    reservedOp lexer "="
    e <- parseTerm
    reserved lexer "in"
    e' <- parseTerm
    return $ RLet n t e e'

parsePi :: Parser Raw
parsePi = do
    (x, t) <- parseParam
    reservedOp lexer "->"
    s <- parseTerm
    return $ RPi x t s

parseApp :: Parser Raw
parseApp = do
    es <- many1 parseAtom
    return $ foldl1 RApp es

parseVar :: Parser Raw
parseVar = RVar <$> parseName


parseTerm :: Parser Raw
parseTerm = try parsePi <|> try parseLam <|> try parseLet <|> try parseApp

parseAtom :: Parser Raw
parseAtom = try parseVar
        <|> try (reserved lexer "_" >> pure RHole)
        <|> try (reserved lexer "Type" >> pure RUni)
        <|> try (parens lexer (parseTerm <* optional (reservedOp lexer ":" >> parseTerm)))


--- untyped elaboration
{-
elab :: Raw -> Trm
elab = elab' []
    where
    elab' :: [Name] -> Raw -> Trm
    elab' env (RVar x) = case indexOf env x of
        Just i -> Var (Idx i)
        Nothing -> error $ "undefined name " ++ x
    elab' env (RLam x e) = Lam x $ elab' (x:env) e
    elab' env (RLet x _ e rest) = Let x (elab' env e) (elab' (x:env) rest)
    elab' env (RApp e1 e2) = App (elab' env e1) (elab' env e2)
-}


--- dealing with levels
lvlToIdx :: Siz -> Lvl -> Idx
lvlToIdx (Lvl siz) (Lvl lvl) = Idx (siz - lvl - 1)

atIdx :: Env -> Idx -> Val
atIdx env (Idx i) = snd $ env !! i

--- beta reduction
vApp :: Val -> Val -> Val
vApp (VLam n _ f) v' = f v'
vApp (VNeu n) v' = VApp n v'
vApp _ _ = error "vApp TODO"

--- normalization by evaluation
eval :: Env -> Trm -> Val
eval env (Lam n t e) = VLam n (eval env t) (\v -> eval ((n, v):env) e)
eval env (Let n _ e e') = eval ((n, eval env e):env) e'
eval env (App e1 e2) = vApp (eval env e1) (eval env e2)
eval env (Var idx) = env `atIdx` idx
eval env (Pi x t s) = VPi x (eval env t) (\v -> eval ((x, v):env) s)
eval env Uni = VUni
eval env (Meta m) = VMeta m

quote :: Siz -> Val -> Trm
quote siz (VLam n t f) = Lam n (quote siz t) $ quote (siz + 1) (f (VVar siz))
quote siz (VApp n v') = App (quote siz (VNeu n)) (quote siz v')
quote siz (VVar lvl) = Var (lvlToIdx siz lvl)
quote siz VUni = Uni
quote siz (VPi x t s) = Pi x (quote siz t) $ quote (siz + 1) (s (VVar siz))
quote siz (VMeta n) = Meta n
quote siz (VNeu _) = error "unreachable, exhaustiveness analysis sucks with pattern synonyms"

normal :: Env -> Trm -> Trm
normal env = quote (Lvl $ length env) . eval env

--- pattern unification
unify :: Ctx -> Val -> Val -> EnvM ()
unify ctx t1 t2 =
    trace ("unify: {"
        ++ intercalate ", " (map (\(a, b) -> "(" ++ a ++ ", " ++ b ++ ")") $ map (bimap id (showVal ctx)) (vals ctx)) ++ " | "
        ++ intercalate ", " (map (\(a, b) -> "(" ++ a ++ ", " ++ b ++ ")") $ map (bimap id (showVal ctx)) (typs ctx)) ++ "}  "
    ++ showVal ctx t1 ++ " ≡ " ++ showVal ctx t2) $ return ()


--- bidirectional elaboration
data Ctx = Ctx { vals :: Env, typs :: Env }
height :: Ctx -> Siz
height Ctx {vals = vs} = Lvl $ length vs

bind :: Ctx -> Name -> VTyp -> Ctx
bind ctx x t = ctx { vals = (x, VVar (height ctx)):vals ctx, typs = (x, t):typs ctx }

checkRLet :: Ctx -> Name -> RTyp -> Raw -> EnvM Ctx
checkRLet ctx x t e = do
    t <- check ctx t VUni
    let vt = eval (vals ctx) t
    e <- check ctx e vt
    let ve = eval (vals ctx) e
    let ctx' = bind ctx x vt
    return ctx'


check :: Ctx -> Raw -> VTyp -> EnvM Trm
check ctx (RLam x e) (VPi y t s) = do
    let ctx' = bind ctx x t
    check ctx' e (s $ VVar (height ctx'))

check ctx (RLet x t e c) s = do
    ctx <- checkRLet ctx x t e
    check ctx c s

check ctx RHole t = newMeta "m"

check ctx raw typ = do
    (trm, typ') <- infer ctx raw
    unify ctx typ' typ
    return trm

infer :: Ctx -> Raw -> EnvM (Trm, VTyp)
infer ctx (RVar x) = case lookupIndex (typs ctx) x of
    Nothing -> error $ "scope error: can't find " ++ x ++ " in context " ++ show (map fst $ typs ctx)
    Just (i, t) -> return (Var (Idx i), t)

infer ctx (RPi x t s) = do
    x <- case x of
        Nothing -> pure ""
        Just n -> pure n
    t <- check ctx t VUni
    let vt = eval (vals ctx) t
    let ctx' = bind ctx x vt
    s <- check ctx' s VUni
    return (Pi x t s, VUni)

infer ctx (RApp r1 r2) = do
    (r1, t1) <- infer ctx r1

    case t1 of
        VPi x t s -> do
{-          Γ ⊢ r1 ⇒ (x : t) -> s(x)
            Γ ⊢ r2 ⇐ t
            -------------------------
            Γ ⊢ (r1 r2) ⇒ s $$ ⟦r2⟧             -}
            r2 <- check ctx r2 t
            let v1 = eval (vals ctx) r2
            return (App r1 r2, s v1)
        t1 -> do
{-          Γ ⊢ r1 ⇒ t1
            fresh x, ?t2, ?s
            t1 ≡ (x : ?t2) -> ?s
            Γ ⊢ r2 ⇐ ?t2
            -------------------------
            Γ ⊢ (r1 r2) ⇒ ?s ⟦r1⟧               -}
            x  <- fresh "x"
            t2 <- eval (        vals ctx) <$> newMeta "t2"
            s  <- eval ((x, t2):vals ctx) <$> newMeta "s"

            r2 <- check ctx r2 t2

            let typ = VPi x t2 (vApp s)
            unify ctx t1 typ

            return (App r1 r2, s)

infer ctx (RLet x t e c) = do
    ctx <- checkRLet ctx x t e
    infer ctx c

infer ctx RHole = do
    x <- newMeta "x"
    t <- eval (vals ctx) <$> newMeta "t"
    return (x, t)

infer ctx (RAnn e t) = do
    t <- check ctx t VUni
    let vt = eval (vals ctx) t
    e <- check ctx e vt
    return (e, vt)

infer ctx RUni = return (Uni, VUni)

infer ctx e = error $ "uninferrable " ++ show e


--- pretty printing
-- instance Show Trm where
--     show = showTerm

-- instance Show Val where
--     show = show . quote 0

showVal :: Ctx -> Val -> String
showVal ctx v = showTerm (map fst $ vals ctx) $ quote (height ctx) v

showTerm :: [Name] -> Trm -> String
showTerm = showTerm' True

showTerm' :: Bool -> [Name] -> Trm -> String
showTerm' toplevel env trm = case trm of
    Lam n t e -> "(λ" ++ rollLam env (Lam n t e) ++ ")"
    Pi n t e -> "(∀" ++ rollLam env (Pi n t e) ++ ")"
    Let n _ e e' -> (if toplevel then "\n" else "")
        ++ "let " ++ n ++ " = "
        ++ showTerm' False env e ++ " in " ++ showTerm' True (n:env) e'
    App e e' -> "(" ++ rollApp env (App e e') ++ ")"
    Var (Idx i) -> env !! i
    Uni -> "Type"
    Meta m -> "?" ++ m

    where
        -- display (λa . (λb . (λc . e))) as (λa b c . e)
        rollLam :: [Name] -> Trm -> String
        rollLam env trm = case trm of
            Lam n t e -> "(" ++ n ++ " : " ++ showTerm env t ++ ") " ++ rollLam (n:env) e
            _         -> ". " ++ showTerm' False env trm

        -- display (((a b) c) d) as (a b c d)
        rollApp :: [Name] -> Trm -> String
        rollApp env trm = case trm of
            App e e' -> rollApp env e ++ " " ++ showTerm' False env e'
            _        -> showTerm' False env trm



--- church numerals
ex1 :: String
ex1 = unlines
    [ "let zero = lam f x . x                           in"
    , "let succ = lam p f x . f (p f x)                 in"
    , "let five = succ (succ (succ (succ (succ zero)))) in"
    , "let add  = lam a b s z . a s (b s z)             in"
    , "let mul  = lam a b s z . a (b s) z               in"
    , "let ten  = add five five                         in"
    , "let hund = mul ten ten                           in"
    , "let thou = mul ten hund                          in"
    , "thou"
    ]



--interpret :: String -> Either ParseError Trm
interpret str = infer (Ctx [] []) <$> parse str

main :: IO ()
main = do
    let ln = "let id : (A : _) -> A -> A = lam T x . x in Type"
    print $ parse ln
    putStrLn ""
    case interpret ln of
        Left err -> print err
        Right envm -> case runEnv envm of
            Left err -> print err
            Right (trm, typ) -> putStrLn $ showTerm [] trm ++ "   :   " ++ showVal (Ctx [] []) typ

--     putStr "λ> "
--     hFlush stdout
--     ln <- getLine
--     when (ln /= "--q") $ do
--         print $ runEnv <$> interpret ln
--         main