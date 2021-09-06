
module Context1 where

import Data.Map qualified as Map

import Name
import Prog1
import Failure
import Polysemy
import Polysemy.Reader
import Polysemy.Error
import Pretty

newtype Context = Context { getContext :: [(Name, Prog)] }
  deriving newtype (Semigroup, Monoid)

type HasContext m = Members '[Reader Context, Error Failure] m

runContext :: Sem (Reader Context : m) a -> Sem m a
runContext = runReader mempty

find :: HasContext m => Name -> Sem m Prog
find n = do
  asks (lookup n . getContext) >>= \case
    Just it -> return it
    Nothing -> throw $ NotFound n

withContext :: HasContext m => [(Name, Prog)] -> Sem m a -> Sem m a
withContext d = do
  local (Context d <>)
