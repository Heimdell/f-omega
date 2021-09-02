
module Name where

import Data.String
import Data.IORef

import System.IO.Unsafe

import Pretty

data Name = Name String Int
  deriving stock (Eq, Ord)
  deriving (Show) via PP Name

instance Pretty Name where
  pp (Name n 0) = pure (text n)
  pp (Name n i) = pure (text n) |.| color black ("'" |.| pp i)

instance IsString Name where fromString = flip Name 0

counter :: IORef Int
counter = unsafePerformIO $ newIORef 0

refresh :: Name -> Name
refresh (Name raw _) = unsafePerformIO do
  modifyIORef counter (+ 1)
  n <- readIORef counter
  return $ Name raw n
