{- | Variable substitution.
-}

module Subst1 where

import Control.Monad.Free

import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Maybe

import Name
import Pretty
import Prog1

import Debug.Trace

-- | The substitution.
--
--   Allows substituting both free and bound variables.
--
newtype Subst = Subst { getSubst :: Map.Map Id Prog }
  deriving newtype (Monoid)

instance Show Subst where
  show (Subst s) = show $ fmap pp s

-- | Merging for substitutions.
--
instance Semigroup Subst where
  Subst s <> Subst t = Subst $ s <> Map.map (subst (Subst s)) t

class Substitutable a where
  subst :: Subst -> a -> a

-- | Run substituions over a program.
--
--   Yes, it is quadratic, thx to `Control.Monad.Free`.
--
--   No, I don't care. Yet.
--
instance Substitutable Prog where
  subst (Subst s) prog = do
    var <- prog                             -- that_feel.jpg
    fromMaybe (Pure var) $ Map.lookup var s

-- | Substitution over a name.
--
instance Substitutable Name where
  subst (Subst s) name =
    case Map.lookup (FreeVar name) s of
      Just (Pure (Bound name')) -> name'  -- I'd call it a hack.
      _                         -> name

-- | Substitution over a pattern.
--
--   We inject bound variables intp patterns to know their index in the alt bodies
--   afterwards (all `refresh`-ed names are unique!).
--
instance Substitutable Pat where
  subst s = \case
    PVar  name   -> PVar (subst s name)
    PCtor c pats -> PCtor c (map (subst s) pats)
    PRec  decls  -> PRec $ flip map decls \decl -> decl { pDeclBody = subst s (pDeclBody decl) }
    other        -> other

-- | Replace given bound name with new value.
--
instantiate :: Name -> Prog -> Prog -> Prog
instantiate name arg = subst (Bound name ==> arg)

-- | Replaces given free name with its bound version.
--
--   This /will not/ overbound stuff, because in @\a -> \a -> a@ in the @\a -> a@
--   this function has already made @a@ bound.
--
capture :: Name -> Subst
capture name = FreeVar name ==> Rigid (refresh name)

-- | Replaces given bound name with datatype/ctor "value".
--
axiom :: Name -> Prog -> Subst
axiom name t = Bound name ==> Axiom name t

-- | Singleton constructor.
--
(==>) :: Id -> Prog -> Subst
var ==> prog = Subst $ Map.singleton var prog

-- | Get all free vars.
--
freeVars :: Prog -> Set Name
freeVars = foldMap \case
  FreeVar n -> Set.singleton n
  _         -> mempty

-- | Check for recursive types.
--
--   Yep, that is not efficient as well.
--
occurs :: Name -> Prog -> Bool
occurs n p = n `Set.member` freeVars p
