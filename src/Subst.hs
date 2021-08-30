
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
  descent    :: Subst -> (Subst -> Type -> Type) -> a -> a
  freeVars :: a -> Set.Set Name

instance Semigroup Subst where
  Subst s <> Subst t = Subst $ s <> Map.map (subst (Subst s)) t

subst :: Substitutable a => Subst -> a -> a
subst s = descent s \(Subst sEnd) -> \case
  TVar n | Just t <- Map.lookup n sEnd -> t
  other                                -> other

substRigid :: Substitutable a => Subst -> a -> a
substRigid s = descent s \(Subst sEnd) -> \case
  TRigid n | Just t <- Map.lookup n sEnd -> t
  other                                  -> other

occurs :: Substitutable a => Name -> a -> Bool
occurs n t = Set.member n (freeVars t)

instance (Substitutable t, Functor f, Foldable f) => Substitutable (f t) where
  descent s = fmap . descent s
  freeVars = foldMap freeVars

instance Substitutable Type where
  descent s r t = case t of
    TVar   {}  -> r s t
    TRigid {}  -> r s t
    TConst {}  -> r s t
    TApp f x   -> TApp (descent s r f) (descent s r x)
    TArr d c   -> TArr (descent s r d) (descent s r c)
    TRec ns    -> TRec (fmap (descent s r) ns)
    TFun n k t -> TFun n k (descent (without n s) r t)
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
  descent s r (n ::= t) = n ::= descent s r t
  freeVars (_ ::= t) = freeVars t

instance Substitutable Prog where
  descent s r = \case
    Var   n     -> Var n
    Sym   n     -> Sym n
    Lam   n t b -> Lam n (descent s r t) (descent s r b)
    App   f x   -> App   (descent s r f) (descent s r x)
    LAM   n t b -> LAM n (descent s r t) (descent (without n s) r b)
    APP   f t   -> APP   (descent s r f) (descent s r t)
    Match o as  -> Match (descent s r o) (descent s r as)
    Rec   ns    -> Rec   (descent s r ns)
    Get   o n   -> Get   (descent s r o) n
    LetRec ds b -> do
      let ns = declNames =<< ds
      let s' = withoutAll ns s
      LetRec (descent s' r ds) (descent s' r b)

    Let d b -> do
      Let (descent s r d) (descent (withoutAll (declNames d) s) r b)

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
  descent s r (Alt pat b) = Alt pat (descent s r b)
  freeVars (Alt _ b) = freeVars b

instance Substitutable Decl where
  descent s r = \case
    Val     n t b         -> Val     n (descent s r t) (descent s r b)
    Capture n             -> Capture n
    Data    n targs ctors -> Data    n (descent s r targs) (descent s r ctors)

  freeVars = \case
    Val     _ t b         -> freeVars t <> freeVars b
    Capture {}            -> mempty
    Data    _ targs ctors -> freeVars targs <> freeVars ctors

instance Substitutable Ctor where
  descent s r (Ctor n ty) = Ctor n (descent s r ty)
  freeVars (Ctor _ ty) = freeVars ty
