{-# LANGUAGE TupleSections #-}
{-# HLINT ignore "Use <$>" #-}

module Surface where

import Control.Monad.Identity    ( Identity, when, liftM2 )

import Text.Parsec               ( Parsec, (<|>), getState, many1, ParseError, runParser, modifyState, SourcePos, try, optional, oneOf, (<?>) )
import Text.Parsec.Token         ( makeTokenParser, GenTokenParser(identifier, parens, reserved, reservedOp), GenLanguageDef (..) )
import Text.Parsec.Language      ( haskellStyle )

import Common.Name               ( Name, name )

-- user facing syntax, emitted by parser
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

--- parsing ---
type Parser a = Parsec String () a

lexer :: GenTokenParser String u Identity
lexer = makeTokenParser $ haskellStyle
    { reservedNames = ["Type", "lam", "let", "in", "_"]
    , reservedOpNames = ["=", ".", ":", "->"]
    }

parse :: String -> Either ParseError Raw
parse = runParser parseTerm () ""


parseName :: Parser Name
parseName = name <$> identifier lexer

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