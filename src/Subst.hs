
module Subst where

import Data.Map qualified as Map
import Data.Set qualified as Set

import Name
import Prog

newtype Subst = Subst { getSubst :: Map.Map Name Type }
  deriving newtype (Eq, Ord, Show, Monoid)

one :: Name -> Type -> Subst
one n t = Subst $ Map.singleton n t

without :: Name -> Subst -> Subst
without n (Subst s) = Subst $ Map.delete n s

withoutAll :: [Name] -> Subst -> Subst
withoutAll = flip (foldr without)

class Substitutable a where
  subst    :: Subst -> a -> a
  freeVars :: a -> Set.Set Name

instance Substitutable Subst where
  subst s1@(Subst s) (Subst t) = Subst $ s <> Map.map (subst s1) t
  freeVars = foldMap freeVars . getSubst

instance Semigroup Subst where
  (<>) = subst

occurs :: Substitutable a => Name -> a -> Bool
occurs n t = Set.member n (freeVars t)

instance (Substitutable t, Functor f, Foldable f) => Substitutable (f t) where
  subst = fmap . subst
  freeVars = foldMap freeVars

instance Substitutable Type where
  subst s@(Subst m) = \case
    TVar n -> case Map.lookup n m of
      Just t  -> t
      Nothing -> TVar n

    TConst n   -> TConst n
    TApp f x   -> TApp (subst s f) (subst s x)
    TArr d c   -> TArr (subst s d) (subst s c)
    TRec ns    -> TRec (fmap (subst s) ns)
    TFun n k t -> TFun n k (subst (without n s) t)
    TStar      -> TStar

  freeVars = \case
    TVar n     -> Set.singleton n
    TConst {}  -> mempty
    TApp f x   -> freeVars f <> freeVars x
    TArr d c   -> freeVars d <> freeVars c
    TRec ns    -> foldMap freeVars ns
    TFun n _ t -> Set.delete n (freeVars t)
    TStar      -> mempty

instance Substitutable TDecl where
  subst s  (n ::= t) = n ::= subst s t
  freeVars (_ ::= t) = freeVars t

instance Substitutable Prog where
  subst s = \case
    Var   n     -> Var n
    Sym   n     -> Sym n
    Lam   n t b -> Lam n (subst s t) (subst s b)
    App   f x   -> App   (subst s f) (subst s x)
    LAM   n t b -> LAM n (subst s t) (subst (without n s) b)
    APP   f t   -> APP   (subst s f) (subst s t)
    Match o as  -> Match (subst s o) (subst s as)
    Rec   ns    -> Rec   (subst s ns)
    Get   o n   -> Get   (subst s o) n
    LetRec ds b -> do
      let ns = declNames =<< ds
      let s' = withoutAll ns s
      LetRec (subst s' ds) (subst s' b)

    Let d b -> do
      Let (subst s d) (subst (withoutAll (declNames d) s) b)

    Lit lit -> Lit lit

  freeVars = \case
    Var    {}    -> mempty
    Sym    {}    -> mempty
    Lam    _ t b -> freeVars t <> freeVars b
    App    f x   -> freeVars f <> freeVars x
    LAM    _ t b -> freeVars t <> freeVars b
    APP    f t   -> freeVars f <> freeVars t
    Match  o as  -> freeVars o <> freeVars as
    Rec    ns    -> freeVars ns
    Get    o _   -> freeVars o
    LetRec ds b  -> freeVars ds <> freeVars b
    Let    d b   -> freeVars d <> freeVars b
    Lit    {}    -> mempty

instance Substitutable Alt where
  subst s (Alt pat b) = Alt pat (subst s b)
  freeVars (Alt _ b) = freeVars b

instance Substitutable Decl where
  subst s = \case
    Val     n t b         -> Val     n (subst s t) (subst s b)
    Capture n             -> Capture n
    Data    n targs ctors -> Data    n (subst s targs) (subst s ctors)

  freeVars = \case
    Val     _ t b         -> freeVars t <> freeVars b
    Capture {}            -> mempty
    Data    _ targs ctors -> freeVars targs <> freeVars ctors

instance Substitutable Ctor where
  subst s (Ctor n ty) = Ctor n (subst s ty)
  freeVars (Ctor _ ty) = freeVars ty
