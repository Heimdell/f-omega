
module Context where

import Data.Map qualified as Map

import Name
import Prog
import Polysemy
import Polysemy.Reader
import Polysemy.Error
import Pretty

newtype Context = Context { getContext :: Map.Map Name Type }
  deriving newtype (Eq, Ord, Semigroup, Monoid)
  deriving (Show) via PP Context

instance Pretty Context where
  pp (Context m) =
    block [pp n |+| ":" |+| pp t | (n, t) <- Map.assocs m] :: Printer

data ContextError
  = NotFound Name
  deriving stock (Show)

instance Pretty ContextError where
  pp (NotFound n) = "name" |+| pp n |+| "is undefined"

type HasContext m = Members '[Reader Context, Error ContextError] m

runContext :: Sem (Reader Context : Error ContextError : m) a -> Sem m (Either ContextError a)
runContext = runError . runReader mempty

find :: HasContext m => Name -> Sem m Type
find n = do
  asks (Map.lookup n . getContext) >>= \case
    Just it -> return it
    Nothing -> throw $ NotFound n

withContext :: HasContext m => [(Name, Type)] -> Sem m a -> Sem m a
withContext d = do
  local (Context (Map.fromList d) <>)
