{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

import Data.List                 ( elemIndex )

import Control.Monad.Identity    ( Identity, when )

import Text.Parsec               ( Parsec, (<|>), getState, many1, ParseError, runParser, modifyState, SourcePos )
import Text.Parsec.Token         ( makeTokenParser, GenTokenParser(identifier, parens, reserved, reservedOp), GenLanguageDef (..) )
import Text.Parsec.Language      ( haskellStyle )

import System.IO                 (hFlush, stdout)



indexOf :: Eq a => [a] -> a -> Maybe Int
indexOf [] _ = Nothing
indexOf (x:xs) y = if x == y then Just 0 else (1+) <$> indexOf xs y



type Name = String

newtype Idx     = Idx     {unIdx  :: Int} deriving (Show, Eq, Num) via Int
newtype Lvl     = Lvl     {unLvl  :: Int} deriving (Show, Eq, Num) via Int
type    Siz = Lvl

newtype MetaVar = MetaVar {unMeta :: Int} deriving (Show, Eq)      via Int

--- user-facing
data Raw = RLam Name Raw
         | RLet Name Raw Raw
         | RApp Raw Raw
         | RVar Name
    deriving (Show)
--- core language
data Trm = Lam Name Trm         -- λn . e
         | Let Name Trm Trm     -- let n = e in e'
         | App Trm Trm          -- (e1 e2)
         | Var Idx
--- semantic domain
data Val = VLam Name (Val -> Val)
         | VNeu Neu
data Neu = NVar Lvl
         | NApp Neu Val

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
    { reservedNames = ["lam", "let", "in"]
    , reservedOpNames = ["=", "."]
    }

parse :: String -> Either ParseError Raw
parse = runParser parseTerm () ""


parseName :: Parser Name
parseName = identifier lexer

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
    reservedOp lexer "="
    e <- parseTerm
    reserved lexer "in"
    e' <- parseTerm
    return $ RLet n e e'


parseApp :: Parser Raw
parseApp = do
    es <- many1 parseAtom
    return $ foldl1 RApp es

parseVar :: Parser Raw
parseVar = RVar <$> parseName



parseTerm :: Parser Raw
parseTerm = parseApp <|> parseLam <|> parseLet

parseAtom :: Parser Raw
parseAtom = parseVar <|> parens lexer parseTerm


--- untyped elaboration
elab :: Raw -> Trm
elab = elab' []
    where
    elab' :: [Name] -> Raw -> Trm
    elab' env (RVar x) = case indexOf env x of
        Just i -> Var (Idx i)
        Nothing -> error $ "undefined name " ++ x
    elab' env (RLam x e) = Lam x $ elab' (x:env) e
    elab' env (RLet x e rest) = Let x (elab' env e) (elab' (x:env) rest)
    elab' env (RApp e1 e2) = App (elab' env e1) (elab' env e2)


--- dealing with levels
lvlToIdx :: Siz -> Lvl -> Idx
lvlToIdx (Lvl siz) (Lvl lvl) = Idx (siz - lvl - 1)

atIdx :: Env -> Idx -> Val
atIdx env (Idx i) = snd $ env !! i

--- beta reduction
vApp :: Val -> Val -> Val
vApp (VLam n f) v' = f v'
vApp (VNeu n) v' = VNeu (NApp n v')

--- normalization by evaluation
eval :: Env -> Trm -> Val
eval env (Lam n e)    = VLam n (\v -> eval ((n, v):env) e)
eval env (Let n e e') = eval ((n, eval env e):env) e'
eval env (App e1 e2)  = vApp (eval env e1) (eval env e2)
eval env (Var idx)    = env `atIdx` idx

quote :: Siz -> Val -> Trm
quote siz (VLam n f)         = Lam n $ quote (siz + 1) (f (VNeu $ NVar siz))
quote siz (VNeu (NApp n v')) = App (quote siz (VNeu n)) (quote siz v')
quote siz (VNeu (NVar lvl))  = Var (lvlToIdx siz lvl)

normal :: Env -> Trm -> Trm
normal env = quote (Lvl $ length env) . eval env




--- pretty printing
instance Show Trm where
    show = showTerm

showTerm :: Trm -> String
showTerm = showTerm' True []
    where
        showTerm' :: Bool -> [Name] -> Trm -> String
        showTerm' toplevel env trm = case trm of
            Lam n e -> "(λ" ++ rollLam env (Lam n e) ++ ")"
            Let n e e' -> (if toplevel then "\n" else "")
                ++ "let " ++ n ++ " = "
                ++ showTerm' False env e ++ " in " ++ showTerm' True (n:env) e'
            App e e' -> "(" ++ rollApp env (App e e') ++ ")"
            Var (Idx i) -> env !! i

        -- display (λa . (λb . (λc . e))) as (λa b c . e)
        rollLam :: [Name] -> Trm -> String
        rollLam env trm = case trm of
            Lam n e -> n ++ " " ++ rollLam (n:env) e
            _         -> ". " ++ showTerm' False env trm

        -- display (((a b) c) d) as (a b c d)
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



interpret :: String -> Either ParseError Trm
interpret str = normal [] . elab <$> parse str

main :: IO ()
main = do
    putStr "λ> "
    hFlush stdout
    ln <- getLine
    when (ln /= "q") $ do
        print $ interpret ln
        main