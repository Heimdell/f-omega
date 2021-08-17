
module Fresh where

import Polysemy
import Polysemy.State
import Name

newtype Fresh = Fresh Int

type HasFreshVars (m :: EffectRow) = Member (State Fresh) m

fresh :: Members '[State Fresh] m => Name -> Sem m Name
fresh (Name n _) = do
  modify \(Fresh f) -> Fresh (f + 1)
  Fresh f <- get
  return $ Name n f

runFresh :: Sem (State Fresh : m) a -> Sem m a
runFresh = evalState (Fresh 0)
