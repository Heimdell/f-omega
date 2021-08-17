
module Name where

import Data.String

import Pretty

data Name = Name String Int
  deriving stock (Eq, Ord)
  deriving (Show) via PP Name

instance Pretty Name where
  pp (Name n 0) = pure (text n)
  pp (Name n i) = pure (text n) |.| "#" |.| pp i

instance IsString Name where fromString = flip Name 0
