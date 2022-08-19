{-# LANGUAGE DerivingVia, PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Data.List                 ( elemIndex, intercalate )
import Data.Bifunctor            ( first, bimap )
import Common.Utils              ( indexOf, lookupIndex )

import Control.Monad.Identity    ( Identity, when, liftM2 )

import System.IO                 ( hFlush, stdout )
import Debug.Trace               ( trace, traceShowId )

import Surface                   ( Raw(..), RTyp, parse )

import Common.Name               ( Name, name, anon, isAnon, fresh, refresh )
import Common.Env                ( EnvM, runEnv )


freshMeta :: Ctx -> VTyp -> EnvM Trm
freshMeta _ _ = Meta <$> fresh

refreshMeta :: Ctx -> VTyp -> String -> EnvM Trm
refreshMeta ctx typ n = do
    m <- refresh (name n)
    trace ("meta: " ++ showCtx ctx ++ " " ++ show m ++ " : " ++ showVal ctx typ) $ return (Meta m)
    

newtype Idx = Idx {unIdx  :: Int} deriving (Show, Eq, Num) via Int
newtype Lvl = Lvl {unLvl  :: Int} deriving (Show, Eq, Num) via Int
type    Siz = Lvl

--- core language
type Spine = [Name]
type Typ = Trm
data Trm = Lam Name Trm         -- λn . e
         | App Trm Trm          -- (e1 e2)
         | Let Name Typ Trm Trm -- let n = e in e'
         | Pi Name Typ Trm      -- Π(x:A).Bx
         | Uni                  -- Type
         | Meta Name            -- ?m
         | Var Idx
--- semantic domain
type VTyp = Val
data Val = VLam Name (Val -> Val)
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
vApp (VLam n f) v' = f v'
vApp (VNeu n) v' = VApp n v'
vApp _ _ = error "vApp TODO"

--- normalization by evaluation
eval :: Env -> Trm -> Val
eval env (Lam n e) = VLam n (\v -> eval ((n, v):env) e)
eval env (Let n _ e e') = eval ((n, eval env e):env) e'
eval env (App e1 e2) = vApp (eval env e1) (eval env e2)
eval env (Var idx) = env `atIdx` idx
eval env (Pi x t s) = VPi x (eval env t) (\v -> eval ((x, v):env) s)
eval env Uni = VUni
eval env (Meta m) = VMeta m

quote :: Siz -> Val -> Trm
quote siz (VLam n f) = Lam n $ quote (siz + 1) (f (VVar siz))
quote siz (VApp n v') = App (quote siz (VNeu n)) (quote siz v')
quote siz (VVar lvl) = Var (lvlToIdx siz lvl)
quote siz VUni = Uni
quote siz (VPi x t s) = Pi x (quote siz t) $ quote (siz + 1) (s (VVar siz))
quote siz (VMeta n) = Meta n
quote siz (VNeu _) = error "unreachable, exhaustiveness analysis sucks with pattern synonyms"

normal :: Env -> Trm -> Trm
normal env = quote (Lvl $ length env) . eval env

--- pattern unification
showCtx :: Ctx -> String
showCtx ctx = "[" -- ++ intercalate ", " (map (\(a, b) -> "(" ++ a ++ ", " ++ b ++ ")") $ map (bimap show (showVal ctx)) (vals ctx)) ++ " | "
        ++ intercalate ", " (map (\(a, b) -> "(" ++ a ++ ", " ++ b ++ ")") $ map (bimap show (showVal ctx)) (typs ctx)) ++ "]"

unify :: Ctx -> Val -> Val -> EnvM ()
unify ctx t1 t2 =
    trace ("unify: " ++ showCtx ctx ++ " " ++ showVal ctx t1 ++ " ≡ " ++ showVal ctx t2) $ return ()


--- bidirectional elaboration
data Ctx = Ctx { vals :: Env, typs :: Env }
height :: Ctx -> Siz
height Ctx {vals = vs} = Lvl $ length vs

bind :: Ctx -> Name -> VTyp -> Ctx
bind ctx x t = ctx { vals = (x, VVar (height ctx)):vals ctx, typs = (x, t):typs ctx }

defn :: Ctx -> Name -> VTyp -> Val -> Ctx
defn ctx x t e = ctx { vals = (x, e):vals ctx, typs = (x, t):typs ctx }

checkRLet :: Ctx -> Name -> RTyp -> Raw -> EnvM (Ctx, Name, Typ, Trm)
checkRLet ctx x t e = do
    t <- check ctx t VUni
    let vt = eval (vals ctx) t
    e <- check ctx e vt
    --let ve = eval (vals ctx) e
    let ctx' = defn ctx x vt (VVar $ height ctx)
    return (ctx', x, t, e)


check :: Ctx -> Raw -> VTyp -> EnvM Trm
check ctx (RLam x e) (VPi y t s) = do
    let ctx' = bind ctx x t
    e <- check ctx' e (s $ VVar (height ctx' - 1))
    return $ Lam x e

check ctx (RLet x t e c) s = do
    (ctx, x, t, e) <- checkRLet ctx x t e
    c <- check ctx c s
    return $ Let x t e c


check ctx RHole t = refreshMeta ctx t "m"

check ctx raw typ = do
    (trm, typ') <- infer ctx raw
    unify ctx typ' typ
    return trm

infer :: Ctx -> Raw -> EnvM (Trm, VTyp)
infer ctx (RVar x) = case (lookupIndex (typs ctx) x, lookupIndex (vals ctx) x) of
    (Just (i, t), Just (j, v)) -> return (quote (height ctx) v, t)
    _ -> error $ "scope error: can't find " ++ show x ++ " in context " ++ show (map fst $ typs ctx)

infer ctx (RPi x t s) = do
    x <- pure $ anon x
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
            Γ ⊢ (r1 r2) ⇒ s ⟦r1⟧                -}
            x  <- refresh $ name "x"
            t2 <- eval (        vals ctx) <$> refreshMeta ctx VUni "t2"
            s  <- eval ((x, t2):vals ctx) <$> refreshMeta ctx VUni "s"

            r2 <- check ctx r2 t2

            let typ = VPi x t2 (vApp s)
            unify ctx t1 typ

            return (App r1 r2, s)

infer ctx (RLet x t e c) = do
    (ctx, x, t, e) <- checkRLet ctx x t e
    (c, s) <- infer ctx c
    return (Let x t e c, s)

infer ctx RHole = do
    t <- eval (vals ctx) <$> refreshMeta ctx VUni "t"
    x <- refreshMeta ctx t "x"
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
--     show = showTerm []
-- 
-- instance Show Val where
--     show = show . quote 0

showVal :: Ctx -> Val -> String
showVal ctx v = showTerm (map fst $ vals ctx) $ quote (height ctx) v

showTerm :: [Name] -> Trm -> String
showTerm = showTerm' True

showTerm' :: Bool -> [Name] -> Trm -> String
showTerm' toplevel env trm = case trm of
    Lam n e -> "(λ" ++ rollLam env (Lam n e) ++ ")"
    Pi n t e -> rollPi env False n t e
    Let n t e e' -> (if toplevel then "\n" else "")
        ++ "let " ++ show n ++ " : " ++ showTerm env t ++ " = "
        ++ showTerm' False env e ++ " in " ++ showTerm' True (n:env) e'
    App e e' -> "(" ++ rollApp env (App e e') ++ ")"
    Var (Idx i) -> show $ env !! i
    Uni -> "Type"
    Meta m -> "?" ++ show m

    where
        -- display (λa . (λb . (λc . e))) as (λa b c . e)
        rollLam :: [Name] -> Trm -> String
        rollLam env trm = case trm of
            Lam n e -> show n ++ " " ++ rollLam (n:env) e
            --Pi n t e -> "(" ++ show n ++ " : " ++ showTerm env t ++ ") " ++ rollLam (n:env) e
            _         -> ". " ++ showTerm' False env trm

        -- display (a -> (b -> (c -> d))) as (a -> b -> c -> d)
        rollPi :: [Name] -> Bool -> Name -> Trm -> Trm -> String
        rollPi env inner n t e = (if inner then "" else "(")
            ++ (if isAnon n
            then showTerm env t
            else "(" ++ show n ++ " : " ++ showTerm env t ++ ")"
            ) ++ " -> " ++ (case e of
                Pi n' t' e' -> rollPi (n:env) True n' t' e'
                _ -> showTerm (n:env) e)
            ++ (if inner then "" else ")")

        -- display (((a b) c) d) as (a b c d)
        rollApp :: [Name] -> Trm -> String
        rollApp env trm = case trm of
            App e e' -> rollApp env e ++ " " ++ showTerm' False env e'
            _        -> showTerm' False env trm



--- untyped church numerals
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

--- holes
ex2 :: String
ex2 = unlines
    [ "let id : (A : _) -> A -> A   = lam T x . x                                in"
    , "let List : Type -> Type      = lam A . (L : _) -> (A -> L -> L) -> L -> L in"
    , "Type"
    ]


--interpret :: String -> Either ParseError Trm
interpret str = infer (Ctx [] []) <$> parse str

main :: IO ()
main = do
    let ln = ex2
    print $ parse ln
    putStrLn ""
    case interpret ln of
        Left err -> print err
        Right envm -> case runEnv envm of
            Left err -> print err
            Right (trm, typ) -> putStrLn $ showTerm [] trm ++ "   :   " ++ showVal (Ctx [] []) typ

    -- putStr "λ> "
    -- hFlush stdout
    -- ln <- getLine
    -- when (ln /= "--q") $ do
    --     print $ runEnv <$> interpret ln
    --     main