
module Name where

import Data.String
import Data.IORef

import System.IO.Unsafe

import Pretty

-- | The name has a refreshable index.
--
data Name = Name String Int
  deriving stock (Eq, Ord)
  deriving (Show) via PP Name

instance Pretty Name where
  pp (Name n 0) = pure (text n)
  pp (Name n i) = pure (text n) |.| color black ({-"'" |.|-} pp i)

instance IsString Name where fromString = flip Name 0

-- | Nothing to see here.
--
--   TODO: use `TVar`.
--
counter :: IORef Int
counter = unsafePerformIO $ newIORef 0

-- | It /magically/ assigns an unique index to the name.
--
refresh :: Name -> Name
refresh (Name raw _) = unsafePerformIO do
  modifyIORef counter (+ 1)
  n <- readIORef counter
  return $ Name raw n
