module Prog1 where

import Control.Monad.Free

import Data.Char (isUpper)
import Data.String (IsString (fromString))
import Data.Function ((&))

import Pretty
import Name

type Prog = Free Prog_ Id

data Prog_ self
  = Lam    (Abstr self)
  | App    self self

  | Pi     (Abstr self)
  | Star

  | Match  self [Alt self]

  | Record [Decl 'NonRec self]
  | TRec   [TDecl self]
  | Get    self Name

  | LetRec [Decl 'IsRec  self] self
  | Let    (Decl 'NonRec self) self

  | Lit    Literal
  | Axiom  Name
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show) via PP (Prog_ self)

data Id
  = FreeVar  Name
  | Bound    Name
  -- | Constant Name
  deriving stock (Eq, Ord)
  deriving (Show) via PP Id

instance IsString Id where
  fromString = FreeVar . fromString

data Abstr self = Abstr Name self self
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  -- deriving (Show) via PP (Abstr self)

data TDecl self = TDecl { tDeclName :: Name, tDeclType :: self }
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show) via PP (TDecl self)

data Decl (rec :: Rec) self
  = Val     Name self self
  | Data    Name [TDecl self] [Ctor self]
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show) via PP (Decl rec self)

data Rec = IsRec | NonRec

data Ctor self = Ctor { ctorName :: Name, ctorType :: self }
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show) via PP (Ctor self)

data Alt self = Alt Pat self
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)
  deriving (Show) via PP (Alt self)

data Pat
  = PVar  Name
  | PCtor Name [Pat]
  | PRec [PDecl]
  | PWild
  | PLit Literal
  -- | PType Type
  deriving stock (Eq, Ord)
  deriving (Show) via PP Pat

instance IsString Pat where
  fromString = PVar . fromString

data PDecl
  = PDecl { pDeclName :: Name, pDeclBody :: Pat }
  deriving stock (Eq, Ord)
  deriving (Show) via PP PDecl

data Literal
  = I Integer
  | F Double
  | S String
  deriving stock (Eq, Ord)
  deriving (Show) via PP Literal

-- declNames :: Decl -> [Name]
-- declNames = \case
--   Val     n _ _  -> [n]
--   Data    n _ cs -> n : fmap ctorName cs
--   Capture _      -> []

kw, punct, aName, aCtor, aLit, aBind, aDecl, aTy, aField, aFlag :: Printer -> Printer
kw     = color (faint  green)
punct  = color         green
aCtor  = color (bright magenta)
aName  = color (faint  yellow)
aFree  = color (bright red)
aTy    = color         blue
aLit   = color (faint  magenta)
aDecl  = color (bright yellow)
aBind  = color         yellow
aField = color (faint  blue)
aFlag  = color         red

collectArgs :: Prog -> ([Either (Name, Prog) (Name, Prog)], Prog)
collectArgs = \case
  Free (Lam (Abstr n t b)) -> do
    let (args, b') = collectArgs b
    (Left (n, t) : args, b')

  other -> ([], other)

ppArg :: Either (Name, Prog) (Name, Prog) -> Printer
ppArg = either (paren . ppArg') (bracket' . ppArg')
  where
    ppArg' (n, t) = aBind (pp n) |+| punct ":" |+| pp' t

instance Pretty Id where
  pp = \case
    FreeVar n -> aFree (pp n)
    Bound   n -> aName (pp n)

instance Pretty1 Prog_ where
  pp1 = \case
    Lam (Abstr n ty body) ->
      par 8 do
        kw "fun" |+| pp n |+| ":" |+| pp ty |+| punct "->" `indent` pp body

    Pi (Abstr n ty body) ->
      par 8 do
        paren (pp n |+| ":" |+| pp ty) |+| punct "->" `indent` pp body

    App f x ->
      par 7 $ prec 8 (pp f) `indent` prec 7 (pp x)

    Match o as -> do
      kw "case" |+| pp' o |+| kw "of"
        `indent` block as

    Record ds -> record ds
    TRec ds -> kw "#" |.| record ds

    Star -> aCtor "*"

    Get p n -> par 3 (prec 4 (pp p) |.| punct "." |.| aField (pp n))

    LetRec ds b ->
      kw "let" |+| aFlag "rec" `indent` block ds
      `above` kw "in" `above` pp' b

    Let d b ->
      (kw "let" `indent` pp' d `above` kw "in")
      `above` pp' b

    Lit l -> pp l

    Axiom n -> aCtor ("'" |.| pp n)

instance Pretty1 (Decl r) where
  pp1 = \case
    Val n t b ->
      aDecl (pp n) |+| punct ":" |+| pp' t |+| punct "="
        `indent` pp' b

    Data n ts ctors ->
      kw "data" |+| aDecl (pp n) |+| ppTArgs ts |+| kw "where"
        `indent` block ctors
      where
        ppTArgs ta = seq' =<< traverse (paren . pp) ta

instance Pretty1 Alt where
  pp1 = \case
    Alt pat b -> do
      punct "|" |+| pp' pat |+| punct "->"
        `indent` pp' b

instance Pretty1 TDecl where
  pp1 (TDecl n t) = aBind (pp n) |+| punct ":" |+| pp t

instance Pretty1 Ctor where
  pp1 (Ctor n ty) =
    punct "|" |+| aCtor (pp n) |+| punct ":" |+| pp ty

instance Pretty Pat where
  pp = \case
    PVar  n      -> aBind (pp n)
    PCtor n pats -> par 6 $ aCtor (pp n) |+| seq' pats
    PRec  ds     -> braces <$> block ds
    PWild        -> aBind "_"
    PLit  l      -> pp l

instance Pretty PDecl where
  pp = \case
    PDecl    n p -> aDecl (pp n) |+| "=" `indent` pp p
    -- PCapture n   -> aBind (pp n)

instance Pretty Literal where
  pp = \case
    I i -> aLit $ pp i
    F d -> aLit $ pp d
    S s -> aLit $ pure $ quotes $ text s

par :: Int -> Printer -> Printer
par = makePar (punct "(", punct ")")

paren :: Printer -> Printer
paren p = punct "(" |.| p |.| punct ")"

bracket' :: Printer -> Printer
bracket' p = punct "{" |.| p |.| punct "}"
