module Prog where

import Data.Char (isUpper)
import Data.String (IsString (fromString))
import Data.Function ((&))

import Pretty
import Name

data Prog
  = Var Name
  | Sym Name

  | Lam Name Type Prog
  | App Prog Prog

  | LAM Name Type Prog
  | APP Prog Type

  | Match Prog [Alt]

  | Rec [Decl]
  | Get Prog Name

  | LetRec [Decl] Prog
  | Let Decl Prog

  | Lit Literal
  deriving stock (Eq, Ord)
  deriving (Show) via PP Prog

instance IsString Prog where fromString = selectCtor Var Sym
instance IsString Type where fromString = selectCtor TVar TConst

selectCtor :: (Name -> a) -> (Name -> a) -> String -> a
selectCtor var sym (c : s)
  | isUpper c = sym $ fromString (c : s)
  | otherwise = var $ fromString(c : s)
selectCtor _ _ _ = error "empty name"


data Type
  = TVar   Name
  -- | TRigid Name
  | TConst Name
  | TApp   Type Type
  | TArr   Type Type
  | TRec   [TDecl]
  | TFun   Name Type Type
  | TStar
  deriving stock (Eq, Ord)
  deriving (Show) via PP Type

data TDecl = (::=) { tDeclName :: Name, tDeclType :: Type }
  deriving stock (Eq, Ord)
  deriving (Show) via PP TDecl

data Decl
  = Val     Name Type Prog
  | Data    Name [TDecl] [Ctor]
  | Capture Name
  deriving stock (Eq, Ord)
  deriving (Show) via PP Decl

data Ctor = Ctor { ctorName :: Name, ctorType :: Type }
  deriving stock (Eq, Ord)
  deriving (Show) via PP Ctor

data Alt = Alt Pat Prog
  deriving stock (Eq, Ord)
  deriving (Show) via PP Alt

data Pat
  = PVar  Name
  | PCtor Name [Pat]
  | PRec [PDecl]
  | PWild
  | PLit Literal
  deriving stock (Eq, Ord)
  deriving (Show) via PP Pat

data PDecl
  = PDecl    Name Pat
  | PCapture Name
  deriving stock (Eq, Ord)
  deriving (Show) via PP PDecl

data Literal
  = I Integer
  | F Double
  | S String
  deriving stock (Eq, Ord)
  deriving (Show) via PP Literal

declNames :: Decl -> [Name]
declNames = \case
  Val     n _ _  -> [n]
  Data    n _ cs -> n : fmap ctorName cs
  Capture _      -> []

kw, punct, aName, aCtor, aLit, aBind, aDecl, aTy, aField, aFlag :: Printer -> Printer
kw     = color (faint  green)
punct  = color         green
aCtor  = color (bright magenta)
aName  = color (faint  yellow)
aTy    = color         blue
aLit   = color (faint  magenta)
aDecl  = color (bright yellow)
aBind  = color         yellow
aField = color (faint  blue)
aFlag  = color         red

collectArgs :: Prog -> ([Either (Name, Type) (Name, Type)], Prog)
collectArgs = \case
  Lam n t b -> do
    let (args, b') = collectArgs b
    (Left (n, t) : args, b')

  LAM n k b -> do
    let (args, b') = collectArgs b
    (Right (n, k) : args, b')

  other -> ([], other)

ppArg :: Either (Name, Type) (Name, Type) -> Printer
ppArg = either (paren . ppArg') (bracket' . ppArg')
  where
    ppArg' (n, t) = aBind (pp n) |+| punct ":" |+| pp' t

instance Pretty Prog where
  pp = \case
    Var n -> aName (pp n)
    Sym n -> aCtor (pp n)
    p@Lam {} ->
      par 8 do
        collectArgs p & \(args, b) ->
          kw "fun" |+| seq' (map ppArg args) |+| punct "->"
            `indent` pp' b

    p@LAM {} ->
      par 8 do
        collectArgs p & \(args, b) ->
          kw "fun" |+| seq' (map ppArg args) |+| punct "->"
            `indent` pp' b

    App f x ->
      par 7 $ prec 8 (pp f) `indent` prec 7 (pp x)

    APP f t ->
      par 7 $ prec 7 (pp f) `indent` (punct "@" |.| prec 0 (pp t))

    Match o as -> do
      kw "case" |+| pp' o |+| kw "of"
        `indent` block as

    Rec ds -> record ds

    Get p n -> par 3 (prec 4 (pp p) |.| punct "." |.| aField (pp n))

    LetRec ds b ->
      kw "let" |+| aFlag "rec" `indent` block ds
      `above` kw "in" `above` pp' b

    Let d b ->
      (kw "let" `indent` pp' d `above` kw "in")
      `above` pp' b

    Lit l -> pp l

instance Pretty Decl where
  pp = \case
    Val n t b ->
      aDecl (pp n) |+| punct ":" |+| pp' t |+| punct "="
        `indent` pp' b

    Capture n -> aDecl (pp n)

    Data n k ctors ->
      kw "data" |+| aDecl (pp n) |+| ppTArgs k |+| kw "where"
        `indent` block ctors
      where
        ppTArgs ta = seq' =<< traverse (paren . pp) ta

instance Pretty Alt where
  pp = \case
    Alt pat b -> do
      punct "|" |+| pp' pat |+| punct "->"
        `indent` pp' b

instance Pretty Type where
  pp = \case
    TVar   n   -> aName (pp n)
    TConst n   -> aTy   (pp n)
    TApp   f x -> par 5 (prec 6 (pp f) |+| prec 5 (pp x))
    TArr   d c -> par 7 (pp d |+| aTy "->" |+| prec 8 (pp c))
    TRec   ds  -> record ds
    TFun   n k t ->
      par 7 do
        paren (aName (pp n) |+| punct ":" |+| pp' k)
          `indent` aTy "->" |+| pp t
    TStar -> aCtor "*"

instance Pretty TDecl where
  pp (n ::= t) = aBind (pp n) |+| punct ":" |+| pp t

instance Pretty Ctor where
  pp (Ctor n ty) =
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
    PCapture n   -> aBind (pp n)

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
