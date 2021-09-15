
module Name where

import Data.String

import Polysemy
import Polysemy.State

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

newtype Fresh = Fresh { getFresh :: Int }

type HasFreshNames (m :: EffectRow) = Members '[State Fresh] m

-- | It /magically/ assigns an unique index to the name.
--
refresh :: HasFreshNames m => Name -> Sem m Name
refresh (Name raw _) = do
  modify $ Fresh . (+ 1) . getFresh
  n <- gets getFresh
  return $ Name raw n

unrefresh :: Name -> Name
unrefresh (Name raw _) = Name raw 0

runFresh :: Sem (State Fresh : m) a -> Sem m a
runFresh = evalState (Fresh 0)
