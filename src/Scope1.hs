
{- | Bunch of smart constructors for the program.
-}
module Scope1 where

import Control.Monad.Free

import Subst1
import Prog1
import Name

import Debug.Trace

-- | Abstract a name over body (but no over the type).
--
abstr :: Name -> Prog -> Prog -> Abstr Prog
abstr name ty body = do
  let s = capture name
  Abstr (subst s name) ty (subst s body)

-- | Create a lambda, capture a name.
--
lam :: Name -> Prog -> Prog -> Prog
lam name ty body = Lam (abstr name ty body)

-- | Create a Pi-type, capture a name.
--
pi_ :: Name -> Prog -> Prog -> Prog
pi_ name ty body = Pi (abstr name ty body)

-- | Make a non-recursive value.
--
val :: Name -> Prog -> Prog -> (Subst, Decl 'NonRec Prog)
val name ty body = do
  let s = capture name
  (s, Val (subst s name) ty (subst s body))

-- | Make a datatype.
--
data_ :: Name -> [TDecl Prog] -> [Ctor Prog] -> (Subst, Decl r Prog)
data_ name targs ctors = do
  let s = capture name <> foldMap (capture . tDeclName) targs -- the name and type arguments become bound
  let (ctorS', ctors') = unzip $ map (ctor s) ctors
  ( s <> mconcat ctorS'
   , Data (subst s name) ((fmap.modifyTDeclName) (subst s) targs) ctors' -- capture type args in ctor types
   )
  where
    modifyTDeclName :: (Name -> Name) -> TDecl Prog -> TDecl Prog
    modifyTDeclName f (TDecl n t) = TDecl (f n) t

-- | Make a constructor.
--
ctor :: Subst -> Ctor Prog -> (Subst, Ctor Prog)
ctor s (Ctor name ty) = do
  let s' = capture name
  (s', Ctor (subst s' name) (subst s ty))

-- | Make a self-referencing value.
--
valRec :: Name -> Prog -> Prog -> (Subst, Decl 'IsRec Prog)
valRec name ty body = do
  let s = capture name
  (s, Val (subst s name) ty (subst s body))

-- | Make a let-expression.
--
let_ :: (Subst, Decl 'NonRec Prog) -> Prog -> Prog
let_ (s, decl) ctx =
  Let decl (subst s ctx)

-- | Make a "let rec"-expression.
--
letRec :: [(Subst, Decl 'IsRec Prog)] -> Prog -> Prog
letRec pack body = do
  let (ss, decls) = unzip pack
  let s = mconcat ss
  -- We only substitute stuff into /bodies/ of decls, not their types.
  LetRec (fmap (substDeclBody s) decls) (subst s body)
  where
    substDeclBody :: Subst -> Decl 'IsRec Prog -> Decl 'IsRec Prog
    substDeclBody s = \case
      Val  name ty   body' -> Val  name ty   (subst s body')
      Data name args ctors -> Data name args (fmap (substCtorType s) ctors)

    substCtorType :: Subst -> Ctor Prog -> Ctor Prog
    substCtorType s (Ctor name ty) = Ctor name (subst s ty)

-- | Make a record.
--
record :: [(Subst, Decl 'NonRec Prog)] -> Prog
record = Record . map snd

-- | Make an alternative.
--
alt :: Pat -> Prog -> Alt Prog
alt pat body = Alt (subst s pat) (subst s body)
  where
    s = patSubst pat

-- | Make a pattern match.
--
match :: Prog -> [Alt Prog] -> Prog
match p alts = Match p alts

-- | Make a star (out of vacuum).
--
star :: Prog
star = Star

-- | Make field access.
--
access :: Prog -> Name -> Prog
access p field = Get p field

-- | Convert pattern into captures.
--
patSubst :: Pat -> Subst
patSubst = \case
  PVar  name   -> capture name
  PCtor _ pats -> foldMap patSubst pats
  PRec  decls  -> foldMap (patSubst . pDeclBody) decls
  _            -> mempty
