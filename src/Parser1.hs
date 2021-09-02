
module Parser1 where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.Monad.Trans.Class

import Data.String
import Data.Bifunctor

import Name
import Prog1
import Subst1
import Scope1
import Pretty qualified

import Text.Parsec hiding ((<|>), many, State)
import Text.Parsec.String
import Text.Parsec.Token

import Debug.Trace

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
  , reservedNames   = words "let rec in case of end _ fun -> @ . : * # ; data where | pi"
  , reservedOpNames = []
  , caseSensitive   = True
  }

mark :: String -> Parser a -> Parser a
mark s act = do
  pos <- getPosition
  -- traceShowM (s <> " " <> show pos)
  act

-- test :: IO ()
-- test = do
--   parseFile parseProg "test.sml" >>= \case
--     Left  err  -> print err
--     Right prog -> print $ Pretty.pp prog

parseFile :: Pretty.Pretty a => Parser a -> String -> IO ()
parseFile p f = do
  t <- readFile f
  print $ second Pretty.pp $ parse (whiteSpace lexer *> p <* eof) f t

parseProg :: Parser Prog
parseProg = mark "prog" parseApp

parseApp :: Parser Prog
parseApp = mark "app" do
  f : xs <- some parseGet
  return $ foldl ((Free .) . App) f xs

parseTerm :: Parser Prog
parseTerm = mark "term"
  do select
      [ Pure <$> parseName
      , parseFunction
      , parsePi
      , parseMatch
      , record <$> braces lexer (parseNonRecDecl `sepBy` comma lexer)
      , parseLet
      , parseLetRec
      , star <$ reserved lexer "*"
      , Free . Lit <$> parseLiteral
      , parens lexer (parseApp)
      , Pure (FreeVar (refresh "hole")) <$ reserved lexer "_"
      ]

parseGet :: Parser Prog
parseGet = mark "get" do
  t <- parseTerm
  ns <- many do
    reserved lexer "."
    parseFieldName
  return $ foldl access t ns

parseFunction :: Parser Prog
parseFunction = mark "fun" do
  reserved lexer "fun"
  args <- some parseArg
  reserved lexer "->"
  body <- parseProg
  return (foldr (uncurry lam) body args)

parsePi :: Parser Prog
parsePi = mark "pi" do
  pure (uncurry pi_)
    <*  reserved lexer "pi"
    <*> try do typeArg <* reserved lexer "->"
    <*> parseProg

parseArg :: Parser (Name, Prog)
parseArg = mark "arg"
  do select
      [ parens lexer (pure (,) <*> parseVar <* reserved lexer ":" <*> parseProg)
      , do
        n <- parseVar
        return (n, Pure $ FreeVar $ refresh "t")
      ]

parseLet :: Parser Prog
parseLet = mark "let" do
  pure let_
    <*  reserved lexer "let"
    <*> parseNonRecDecl
    <*  reserved lexer "in"
    <*> parseProg

parseLetRec :: Parser Prog
parseLetRec = mark "let rec" do
  pure letRec
    <*  reserved lexer "let"
    <*  reserved lexer "rec"
    <*> some parseDecl
    <*  reserved lexer "in"
    <*> parseProg

parseDecl :: Parser (Subst, Decl 'IsRec Prog)
parseDecl = mark "decl"
  do select
      [ pure data_
          <*  reserved lexer "data"
          <*> parseCtor
          <*> many (parens lexer parseTDecl)
          <*  reserved lexer "where"
          <*> many parseCtorDecl

      , pure valRec
          <*> parseFieldName
          <*> select
            [ reserved lexer ":" *> parseProg
            , return $ Pure $ FreeVar $ refresh "t"
            ]
          <*  reserved lexer "="
          <*> parseProg
      ]

parseNonRecDecl :: Parser (Subst, Decl 'NonRec Prog)
parseNonRecDecl = mark "nrd"
  do select
      [ pure data_
          <*  reserved lexer "data"
          <*> parseCtor
          <*> many (parens lexer parseTDecl)
          <*  reserved lexer "where"
          <*> many parseCtorDecl

      , pure val
          <*> parseFieldName
          <*> select
            [ reserved lexer ":" *> parseProg
            , return $ Pure $ FreeVar $ refresh "t"
            ]
          <*  reserved lexer "="
          <*> parseProg
      ]

parseMatch :: Parser Prog
parseMatch = mark "match" do
  pure match
    <*  reserved lexer "case"
    <*> parseProg
    <*  reserved lexer "of"
    <*> many parseAlt

parseAlt :: Parser (Alt Prog)
parseAlt = mark "alt" do
  pure Alt
    <*  reserved lexer "|"
    <*> parsePat
    <*  reserved lexer "->"
    <*> parseProg

parseTDecl :: Parser (TDecl Prog)
parseTDecl = mark "tdecl" do
  pure TDecl
    <*> parseVar
    <*  reserved lexer ":"
    <*> parseProg

typeArg :: Parser (Name, Prog)
typeArg = mark "targ" do
  parens lexer do
    pure (,)
      <*> mark "targ/tvar" do parseVar
      <*  reserved lexer ":"
      <*> parseProg

parseCtorDecl :: Parser (Ctor Prog)
parseCtorDecl = mark "ctor" do
  pure Ctor
    <*  reserved lexer "|"
    <*> parseCtor
    <*  reserved lexer ":"
    <*> parseProg

parsePat :: Parser Pat
parsePat = mark "pat" do
  n  <- parseCtor
  ps <- many parsePatTerm
  return $ PCtor n ps

parseName :: Parser Id
parseName = try do
  n <- identifier lexer
  return $ fromString n

parseCtor :: Parser Name
parseCtor = try do
  n <- identifier lexer
  guard (head n `elem` (['A'.. 'Z'] ++ ":"))
  return $ fromString n

parseFieldName :: Parser Name
parseFieldName = try do
  n <- identifier lexer
  return $ fromString n

parseVar :: Parser Name
parseVar = try do
  n <- identifier lexer
  return $ fromString n

parsePatTerm :: Parser Pat
parsePatTerm = select
  [ PVar  <$> parseVar
  , PRec  <$> braces lexer (parsePDecl `sepBy` comma lexer)
  , PWild <$  reserved lexer "_"
  , PLit  <$> parseLiteral
  -- , PType <$> parseProg
  ]

parsePDecl :: Parser PDecl
parsePDecl =
  pure PDecl
    <*> parseVar
    <*  reserved lexer "="
    <*> parsePat

parseLiteral :: Parser Literal
parseLiteral = select
  [ F <$> try (float lexer)
  , I <$> decimal lexer
  , S <$> stringLiteral lexer
  ] <* whiteSpace lexer

select :: Alternative f => [f a] -> f a
select = foldr (<|>) empty

class Subtype a t where
  inject :: a -> t
  project :: t -> Maybe a

pattern Is :: Subtype a t => a -> t
pattern Is a <- (project -> Just a) where
  Is t = inject t

instance Subtype a a where
  inject = id
  project = Just
