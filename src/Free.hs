
module Free where

-- import Control.Monad

-- import Data.String

-- import Pretty

-- data Free f a
--   = Pure a
--   | Join (f (Free f a))

-- instance IsString a => IsString (Free f a) where
--   fromString = Pure . fromString

-- instance Functor f => Functor (Free f) where
--   fmap = liftM

-- instance Functor f => Applicative (Free f) where
--   pure = Pure
--   (<*>) = ap

-- instance Functor f => Monad (Free f) where
--   Pure a >>= f = f a
--   Join free >>= f = Join (fmap (>>= f) free)

-- instance (forall a. Eq a => Eq (f a), Eq b) => Eq (Free f b) where
--   Pure a == Pure b = a == b
--   Join a == Join b = a == b
--   _      == _      = False

-- instance
--   ( forall a. (Ord a, Eq a) => Ord (f a)
--   , forall a. Eq a => Eq (f a)
--   , Ord b
--   ) => Ord (Free f b) where
--     compare (Pure a) (Pure b) = compare a b
--     compare (Join a) (Join b) = compare a b
--     compare (Pure _) (Join _) = LT
--     compare  _        _       = GT

-- instance (forall a. (Show a, Pretty a) => Show (f a), Show b) => Show (Free f b) where
--   show (Pure a) = show a
--   show (Join a) = show a

-- instance (forall a. Pretty a => Pretty (f a), Pretty b) => Pretty (Free f b) where
--   pp (Pure a) = pp a
--   pp (Join a) = pp a
