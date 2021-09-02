
module Scope1 where

import Control.Monad.Free

import Subst1
import Prog1
import Name

import Debug.Trace

abstr :: Name -> Prog -> Prog -> Abstr Prog
abstr name ty body = do
  let s = capture name
  Abstr (subst s name) ty (subst s body)

lam :: Name -> Prog -> Prog -> Prog
lam name ty body = Free $ Lam (abstr name ty body)

pi_ :: Name -> Prog -> Prog -> Prog
pi_ name ty body = Free $ Pi (abstr name ty body)

val :: Name -> Prog -> Prog -> (Subst, Decl 'NonRec Prog)
val name ty body = do
  let s = capture name
  (s, Val (subst s name) ty (subst s body))

data_ :: Name -> [TDecl Prog] -> [Ctor Prog] -> (Subst, Decl r Prog)
data_ name targs ctors = do
  let s = capture name <> foldMap (capture . tDeclName) targs
  let (ctorS', ctors') = unzip $ map (ctor s) ctors
  ( s <> mconcat ctorS'
   , Data (subst s name) ((fmap.modifyTDeclName) (subst s) targs) ctors'
   )
  where
    modifyTDeclName :: (Name -> Name) -> TDecl Prog -> TDecl Prog
    modifyTDeclName f (TDecl n t) = TDecl (f n) t

ctor :: Subst -> Ctor Prog -> (Subst, Ctor Prog)
ctor s (Ctor name ty) = do
  let s' = capture name
  (s', Ctor (subst s' name) (subst s ty))

valRec :: Name -> Prog -> Prog -> (Subst, Decl 'IsRec Prog)
valRec name ty body = do
  let s = capture name
  (s, Val (subst s name) ty (subst s body))

let_ :: (Subst, Decl 'NonRec Prog) -> Prog -> Prog
let_ (s, decl) ctx =
  Free $ Let decl (subst s ctx)

letRec :: [(Subst, Decl 'IsRec Prog)] -> Prog -> Prog
letRec pack body = do
  let (ss, decls) = unzip pack
  let s = mconcat ss
  Free $ LetRec (fmap (substDeclBody s) decls) (subst s body)
  where
    substDeclBody :: Subst -> Decl 'IsRec Prog -> Decl 'IsRec Prog
    substDeclBody s = \case
      Val  name ty   body' -> Val  name ty   (subst s body')
      Data name args ctors -> Data name args (fmap (substCtorType s) ctors)

    substCtorType :: Subst -> Ctor Prog -> Ctor Prog
    substCtorType s (Ctor name ty) = Ctor name (subst s ty)

record :: [(Subst, Decl 'NonRec Prog)] -> Prog
record = Free . Record . map snd

alt :: Pat -> Prog -> Alt Prog
alt pat body = Alt (subst s pat) (subst s body)
  where
    s = patSubst pat

match :: Prog -> [Alt Prog] -> Prog
match p alts = Free $ Match p alts

star :: Prog
star = Free Star

access :: Prog -> Name -> Prog
access p field = Free $ Get p field

patSubst :: Pat -> Subst
patSubst = \case
  PVar  name   -> capture name
  PCtor _ pats -> foldMap patSubst pats
  PRec  decls  -> foldMap (patSubst . pDeclBody) decls
  _            -> mempty
