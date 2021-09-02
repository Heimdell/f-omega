
module Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class

import Data.String

import Polysemy
import Polysemy.State (State)

import Name
import Prog
import Fresh

import Text.Parsec hiding ((<|>), many, State)
import Text.Parsec.String
import Text.Parsec.Token

lexer :: Stream s m Char => GenTokenParser s u m
lexer = makeTokenParser LanguageDef
  { commentStart    = "{-"
  , commentEnd      = "-}"
  , commentLine     = "--"
  , nestedComments  = True
  , identStart      = oneOf $ ['a'.. 'z'] ++ ['A'.. 'Z'] ++ "!~<>#.@$%^&*-+=:;\\/?_"
  , identLetter     = oneOf $ ['a'.. 'z'] ++ ['A'.. 'Z'] ++ "!~<>#.@$%^&*-+=:;\\/?_" ++ ['0'.. '9']
  , opStart         = empty
  , opLetter        = empty
  , reservedNames   = words "let rec in case of end _ fun -> @ . : * # ; data where |"
  , reservedOpNames = []
  , caseSensitive   = True
  }

type Parser' m a = ParsecT String () (Sem m) a

parseFile :: Parser' [State Fresh, Embed IO] a -> String -> IO (Either ParseError a)
parseFile p f = do
  t <- readFile f
  runM $ runFresh $ runParserT (whiteSpace lexer *> p <* eof) () f t

parseProg :: HasFreshVars m => Parser' m Prog
parseProg = parseApp

parseTerm :: HasFreshVars m => Parser' m Prog
parseTerm = select
  [ Var <$> parseVar
  , Sym <$> parseCtor
  , parseFunction
  , parseMatch
  , Rec <$> braces lexer (parseDecl `sepBy` comma lexer)
  , parseLet
  , parseLetRec
  , Lit <$> parseLiteral
  , parens lexer (parseApp)
  ]

parseApp :: HasFreshVars m => Parser' m Prog
parseApp = do
  f : xs <- some parseGet
  return $ foldl App f xs

parseGet :: HasFreshVars m => Parser' m Prog
parseGet = do
  t <- parseTerm
  ns <- many do
    reserved lexer "."
    parseVar
  return $ foldl Get t ns

parseFunction :: HasFreshVars m => Parser' m Prog
parseFunction = do
  reserved lexer "fun"
  args <- some parseArg
  reserved lexer "->"
  body <- parseProg
  -- reserved lexer "end"
  return (foldr lam body args)
  where
    lam (True, (n, t)) b = LAM n t b
    lam (_,    (n, t)) b = Lam n t b

parseArg :: HasFreshVars m => Parser' m (Bool, (Name, Type))
parseArg = select
  [ (,) True  <$> braces lexer (pure (,) <*> parseVar <* reserved lexer ":" <*> parseType)
  , (,) False <$> parens lexer (pure (,) <*> parseVar <* reserved lexer ":" <*> parseType)
  , (,) False <$> do
    n <- parseVar
    t <- lift do fresh n
    return (n, TVar t)
  ]

parseLet :: HasFreshVars m => Parser' m Prog
parseLet =
  pure Let
    <*  reserved lexer "let"
    <*> parseDecl
    <*  reserved lexer "in"
    <*> parseProg

parseLetRec :: HasFreshVars m => Parser' m Prog
parseLetRec =
  pure LetRec
    <*  reserved lexer "let"
    <*  reserved lexer "rec"
    <*> some parseDecl
    <*  reserved lexer "in"
    <*> parseProg

parseDecl :: HasFreshVars m => Parser' m Decl
parseDecl = select
  [ pure Data
      <*  reserved lexer "data"
      <*> parseCtor
      <*> many (parens lexer parseTDecl)
      <*  reserved lexer "where"
      <*> many parseCtorDecl

  , pure Val
      <*> parseVar
      <*> select
        [ reserved lexer ":" *> parseType
        , TVar <$> lift do fresh "t"
        ]
      <*  reserved lexer "="
      <*> parseProg
  ]

parseMatch :: HasFreshVars m => Parser' m Prog
parseMatch =
  pure Match
    <*  reserved lexer "case"
    <*> parseProg
    <*  reserved lexer "of"
    <*> many parseAlt

parseAlt :: HasFreshVars m => Parser' m Alt
parseAlt =
  pure Alt
    <*  reserved lexer "|"
    <*> parsePat
    <*  reserved lexer "->"
    <*> parseProg

parseType :: HasFreshVars m => Parser' m Type
parseType = do
  parseTypeArrow

parseTypeArrow :: HasFreshVars m => Parser' m Type
parseTypeArrow = select
  [ pure (uncurry TFun)
      <*> try do typeArg <* reserved lexer "->"
      <*> parseType

  , pure TArr
      <*> try do typeApp <* reserved lexer "->"
      <*> parseType

  , typeApp
  ]

typeApp :: HasFreshVars m => Parser' m Type
typeApp = do
  f : xs <- some typeTerm
  return (foldl TApp f xs)

typeTerm :: HasFreshVars m => Parser' m Type
typeTerm = select
  [ parens lexer parseType
  , TStar  <$  reserved lexer "*"
  , TVar   <$> parseVar
  , TConst <$> parseCtor
  , TRec   <$> do reserved lexer "#" *> braces lexer (parseTDecl `sepBy` comma lexer)
  ]

parseTDecl :: HasFreshVars m => Parser' m TDecl
parseTDecl =
  pure (::=)
    <*> parseName
    <*  reserved lexer ":"
    <*> parseType

typeArg :: HasFreshVars m => Parser' m (Name, Type)
typeArg = parens lexer do
  pure (,)
    <*> parseVar
    <*  reserved lexer ":"
    <*> parseType

parseCtorDecl :: HasFreshVars m => Parser' m Ctor
parseCtorDecl =
  pure Ctor
    <*  reserved lexer "|"
    <*> parseCtor
    <*  reserved lexer ":"
    <*> parseType

parsePat :: HasFreshVars m => Parser' m Pat
parsePat = do
  n  <- parseCtor
  ps <- many parsePatTerm
  return $ PCtor n ps

parseCtor :: HasFreshVars m => Parser' m Name
parseCtor = try do
  n <- identifier lexer
  guard (head n `elem` (['A'.. 'Z'] ++ ":"))
  return $ fromString n

parseVar :: HasFreshVars m => Parser' m Name
parseVar = try do
  n <- identifier lexer
  guard (head n `notElem` (['A'.. 'Z'] ++ ":"))
  return $ fromString n

parseName :: HasFreshVars m => Parser' m Name
parseName = try do
  n <- identifier lexer
  return $ fromString n

parsePatTerm :: HasFreshVars m => Parser' m Pat
parsePatTerm = select
  [ PVar  <$> parseVar
  , PRec  <$> braces lexer (parsePDecl `sepBy` comma lexer)
  , PWild <$  reserved lexer "_"
  , PLit  <$> parseLiteral
  -- , PType <$> parseType
  ]

parsePDecl :: HasFreshVars m => Parser' m PDecl
parsePDecl =
  pure PDecl
    <*> parseName
    <*  reserved lexer "="
    <*> parsePat

parseLiteral :: HasFreshVars m => Parser' m Literal
parseLiteral = select
  [ F <$> try (float lexer)
  , I <$> decimal lexer
  , S <$> stringLiteral lexer
  ] <* whiteSpace lexer

select :: Alternative f => [f a] -> f a
select = foldr (<|>) empty
