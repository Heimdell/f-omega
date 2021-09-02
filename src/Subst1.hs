
module Subst1 where

import Control.Monad.Free

import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Maybe

import Name
import Pretty
import Prog1

import Debug.Trace

newtype Subst = Subst { getSubst :: Map.Map Id Prog }
  deriving newtype (Monoid)

instance Show Subst where
  show (Subst s) = show $ fmap pp s

instance Semigroup Subst where
  Subst s <> Subst t = Subst $ s <> Map.map (subst (Subst s)) t

class Substitutable a where
  subst :: Subst -> a -> a

instance Substitutable Prog where
  subst (Subst s) prog = do
    var <- prog
    fromMaybe (Pure var) $ Map.lookup var s

instance Substitutable Name where
  subst (Subst s) name =
    case Map.lookup (FreeVar name) s of
      Just (Pure (Bound name')) -> name'
      _                         -> name

instance Substitutable Pat where
  subst s = \case
    PVar  name   -> PVar (subst s name)
    PCtor c pats -> PCtor c (map (subst s) pats)
    PRec  decls  -> PRec $ flip map decls \decl -> decl { pDeclBody = subst s (pDeclBody decl) }
    other        -> other

instantiate :: Name -> Prog -> Prog -> Prog
instantiate name arg = subst (Bound name ==> arg)

capture :: Name -> Subst
capture name = FreeVar name ==> Pure (Bound (refresh name))

axiom :: Name -> Subst
axiom name = Bound name ==> Free (Axiom name)

(==>) :: Id -> Prog -> Subst
var ==> prog = Subst $ Map.singleton var prog


-- one :: Name -> Type -> Subst
-- one n t = Subst $ Map.singleton n t

-- without :: Name -> Subst -> Subst
-- without n (Subst s) = Subst $ Map.delete n s

-- withoutAll :: [Name] -> Subst -> Subst
-- withoutAll = flip (foldr without)

-- class Substitutable a where
--   subst    :: Subst -> a -> a
--   freeVars :: a -> Set.Set Name

-- instance Semigroup Subst where
--   Subst s <> Subst t = Subst $ s <> Map.map (subst (Subst s)) t

-- occurs :: Substitutable a => Name -> a -> Bool
-- occurs n t = Set.member n (freeVars t)

-- instance (Substitutable t, Functor f, Foldable f) => Substitutable (f t) where
--   subst = fmap . subst
--   freeVars = foldMap freeVars

-- instance Substitutable Type where
--   subst s t = case t of
--     TVar   n   -> maybe (TVar n) id $ Map.lookup n (getSubst s)
--     TRigid {}  -> t
--     TConst {}  -> t
--     TApp f x   -> TApp (subst s f) (subst s x)
--     TArr d c   -> TArr (subst s d) (subst s c)
--     TRec ns    -> TRec (fmap (subst s) ns)
--     TFun n k t -> TFun n k (subst (without n s) t)
--     TStar      -> TStar

--   freeVars = \case
--     TVar n     -> Set.singleton n
--     TConst {}  -> mempty
--     TApp f x   -> freeVars f <> freeVars x
--     TArr d c   -> freeVars d <> freeVars c
--     TRec ns    -> foldMap freeVars ns
--     TFun n _ t -> Set.delete n (freeVars t)
--     TStar      -> mempty

-- instance Substitutable TDecl where
--   subst s (n ::= t) = n ::= subst s t
--   freeVars (_ ::= t) = freeVars t

-- instance Substitutable Prog where
--   subst s = \case
--     Var   n     -> Var n
--     Sym   n     -> Sym n
--     Lam   n t b -> Lam n  (subst s t) (subst s b)
--     App   f x   -> App    (subst s f) (subst s x)
--     LAM   n t b -> LAM n  (subst s t) (subst (without n s) b)
--     APP   f t   -> APP    (subst s f) (subst s t)
--     Match o as  -> Match  (subst s o) (subst s as)
--     Rec   ns    -> Rec    (subst s ns)
--     Get   o n   -> Get    (subst s o) n
--     LetRec ds b -> LetRec (subst s ds) (subst s b)
--     Let    d  b -> Let    (subst s d)  (subst s b)

--     Lit lit -> Lit lit

--   freeVars = \case
--     Var    {}    -> mempty
--     Sym    {}    -> mempty
--     Lam    _ t b -> freeVars t <> freeVars b
--     App    f x   -> freeVars f <> freeVars x
--     LAM    _ t b -> freeVars t <> freeVars b
--     APP    f t   -> freeVars f <> freeVars t
--     Match  o as  -> freeVars o <> freeVars as
--     Rec    ns    -> freeVars ns
--     Get    o _   -> freeVars o
--     LetRec ds b  -> freeVars ds <> freeVars b
--     Let    d b   -> freeVars d <> freeVars b
--     Lit    {}    -> mempty

-- instance Substitutable Alt where
--   subst s (Alt pat b) = Alt pat (subst s b)
--   freeVars (Alt _ b) = freeVars b

-- instance Substitutable Decl where
--   subst s = \case
--     Val     n t b         -> Val     n (subst s t) (subst s b)
--     Capture n             -> Capture n
--     Data    n targs ctors -> Data    n (subst s targs) (subst (withoutAll (map tDeclName targs) s) ctors)

--   freeVars = \case
--     Val     _ t b         -> freeVars t <> freeVars b
--     Capture {}            -> mempty
--     Data    _ targs ctors -> freeVars targs <> freeVars ctors

-- instance Substitutable Ctor where
--   subst s (Ctor n ty) = Ctor n (subst s ty)
--   freeVars (Ctor _ ty) = freeVars ty
