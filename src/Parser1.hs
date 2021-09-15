
module Parser1 where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class

import Data.String
import Data.Bifunctor

import Polysemy
import Polysemy.State

import Name
import Prog1
import Subst1
import Scope1
import Pretty qualified
import Eval1

import Text.Parsec hiding ((<|>), many, State, Parser)
-- import Text.Parsec.String
import Text.Parsec.Token

-- import Debug.Trace

lexer :: GenTokenParser String () (Sem '[State Fresh])
lexer = makeTokenParser LanguageDef
  { commentStart    = "{-"
  , commentEnd      = "-}"
  , commentLine     = "--"
  , nestedComments  = True
  , identStart      = oneOf $ ['a'.. 'z'] ++ ['A'.. 'Z'] ++ "!~<>#@$%^&*-+=:;\\/?_"
  , identLetter     = oneOf $ ['a'.. 'z'] ++ ['A'.. 'Z'] ++ "!~<>#@$%^&*-+=:;\\/?_" ++ ['0'.. '9']
  , opStart         = oneOf "."
  , opLetter        = oneOf "."
  , reservedNames   = words "let rec in case of end _ fun -> @ : * # ; data where | pi ffi"
  , reservedOpNames = words "."
  , caseSensitive   = True
  }

type Parser = ParsecT String () (Sem '[State Fresh])

mark :: String -> Parser a -> Parser a
mark _s act = do
  _pos <- getPosition
  -- traceShowM (s <> " " <> show pos)
  act

-- test :: IO ()
-- test = do
--   parseFile parseProg "test.sml" >>= \case
--     Left  err  -> print err
--     Right prog -> print $ Pretty.pp prog

parseFile :: (Pretty.Pretty a, Eval1.Evals a) => Parser a -> String -> IO (Either ParseError a)
parseFile p f = do
  t <- readFile f
  let p' = whiteSpace lexer *> p <* eof
  return
    $ run
    $ evalState (Fresh 0)
    $ runParserT p' () f t

parseProg :: Parser Prog
parseProg = mark "prog" parseApp

parseApp :: Parser Prog
parseApp = mark "app" do
  f : xs <- some parseGet
  return $ foldl App f xs

parseTerm :: Parser Prog
parseTerm = mark "term"
  do select
      [ Var <$> parseVar
      , parseFunction
      , parsePi
      , parseMatch
      , record <$> braces lexer (parseNonRecDecl `sepBy` comma lexer)
      , pure Product <* reserved lexer "#" <*> braces lexer (parseTDecl `sepBy` comma lexer)
      , parseLet
      , parseLetRec
      , star <$ reserved lexer "*"
      , Lit  <$> parseLiteral
      , parens lexer parseApp
      , parseHole
      , parseFFI
      ]

parseHole :: Parser Prog
parseHole = do
  var <- lift $ refresh "hole"
  Var var <$ reserved lexer "_"

parseFFI :: Parser Prog
parseFFI = do
  reserved lexer "ffi"
  n <- parseVar
  reserved lexer ":"
  t <- parseProg
  return $ FFI n t

parseGet :: Parser Prog
parseGet = mark "get" do
  t <- parseTerm
  ns <- many do
    reservedOp lexer "."
    parseFieldName
  return $ foldl access t ns

parseFunction :: Parser Prog
parseFunction = mark "fun" do
  reserved lexer "fun"
  args <- some parseArg
  reserved lexer "->"
  body <- parseProg
  foldM lam' body args
  where
    lam' b (n, t) = lift $ lam n t b

parsePi :: Parser Prog
parsePi = mark "pi" do
  reserved lexer "pi"
  (n, t) <- try do typeArg <* reserved lexer "->"
  b      <- parseProg
  lift $ pi_ n t b

parseArg :: Parser (Name, Prog)
parseArg = mark "arg"
  do select
      [ parens lexer (pure (,) <*> parseVar <* reserved lexer ":" <*> parseProg)
      , do
        n <- parseVar
        u <- lift $ refresh "u"
        return (n, Var u)
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

parseAnyDecl
  :: ( Name
     -> Prog
     -> Prog
     -> Sem '[State Fresh] (Subst, Decl r Prog)
     )
  -> Parser (Subst, Decl r Prog)
parseAnyDecl valDecl = mark "decl"
  do select
      [ do
          reserved lexer "data"
          n   <- parseCtor
          tas <- many (parens lexer parseTDecl)
          reserved lexer "where"
          cs  <- many parseCtorDecl
          lift $ data_ n tas cs

      , do
          n <- parseFieldName
          t <- select
            [ reserved lexer ":" *> parseProg
            , do
                s <- lift $ refresh "s"
                return $ Var s
            ]
          reserved lexer "="
          b <- parseProg
          lift $ valDecl n t b
      ]

parseDecl :: Parser (Subst, Decl 'IsRec Prog)
parseDecl = parseAnyDecl valRec

parseNonRecDecl :: Parser (Subst, Decl 'NonRec Prog)
parseNonRecDecl = parseAnyDecl val

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
