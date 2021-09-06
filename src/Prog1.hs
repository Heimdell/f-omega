module Prog1 where

import Control.Monad.Free

import Data.Char (isUpper)
import Data.String (IsString (fromString))
import Data.Function ((&))

import Pretty
import Name

type Prog = Free Prog_ Id

data Prog_ self
  = Lam_     (Abstr self)
  | App_     self self

  | Pi_      (Abstr self)
  | Star_

  | Match_   self [Alt self]

  | Record_  [Decl 'NonRec self]
  | Product_ [TDecl self]
  | Get_     self Name

  | LetRec_  [Decl 'IsRec  self] self
  | Let_     (Decl 'NonRec self) self

  | Lit_     Literal
  | Axiom_   Name self
  | FFI_     Name self
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)

instance {-# overlaps #-} Show Prog where
  show = show . pp

{-# complete Var, Rigid, Lam, App, Pi, Star, Match, Record, Product, Get, LetRec, Let, Lit, Axiom, FFI #-}

pattern Var     n      = Pure (FreeVar  n)
pattern Rigid   n      = Pure (Bound    n)
pattern Lam     a      = Free (Lam_     a)
pattern App     f x    = Free (App_     f x)
pattern Pi      a      = Free (Pi_      a)
pattern Star           = Free  Star_
pattern Match   p alts = Free (Match_   p alts)
pattern Record  ds     = Free (Record_  ds)
pattern Product ts     = Free (Product_ ts)
pattern Get     o f    = Free (Get_     o f)
pattern LetRec  ds b   = Free (LetRec_  ds b)
pattern Let     d b    = Free (Let_     d b)
pattern Lit     i      = Free (Lit_     i)
pattern Axiom   n t    = Free (Axiom_   n t)
pattern FFI     n t    = Free (FFI_     n t)

telescope :: [TDecl Prog] -> Prog -> Prog
telescope tas b = foldr makePi b tas
  where
    makePi (TDecl n t) b' = Pi $ Abstr n t b'

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
  Lam (Abstr n t b) -> do
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

instance Pretty Prog where
  pp = \case
    Var   n -> aFree (pp n)
    Rigid n -> aName (pp n)

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
    Product ds -> kw "#" |.| record ds

    Star -> aCtor "*"

    Get p n -> par 3 (prec 4 (pp p) |.| punct "." |.| aField (pp n))

    LetRec ds b ->
      kw "let" |+| aFlag "rec" `indent` block ds
      `above` kw "in" `above` pp' b

    Let d b ->
      (kw "let" `indent` pp' d `above` kw "in")
      `above` pp' b

    Lit l -> pp l

    Axiom n _ -> aCtor ("'" |.| pp n)
    FFI   n _ -> aCtor ("'" |.| pp n)

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
