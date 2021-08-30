
module Unify where

import Data.Set qualified as Set
import Data.Traversable
import Data.Foldable (for_)

import Polysemy
import Polysemy.Error
import Polysemy.State hiding (Get)
import Polysemy.Reader

import Name
import Prog
import Fresh
import Subst
import Pretty
import Context

import Debug.Trace qualified as Debug

type Unifies m =
  ( Members '[Error UnificationError, State Subst] m
  , HasFreshVars m
  )

evalUnification
  :: forall m a
  .  Sem (Error UnificationError : State Subst : m) a
  -> Sem m (Either UnificationError a)
evalUnification = evalState mempty . runError

runUnification
  :: forall m a
  .  Sem (Error UnificationError : State Subst : m) a
  -> Sem m (Subst, Either UnificationError a)
runUnification = runState mempty . runError

applyBindings :: (Unifies m, Substitutable t) => t -> Sem m t
applyBindings t = do
  s <- get @Subst
  return (subst s t)

data UnificationError
  = Mismatch Type Type
  | Occurs Name Type
  | ExpectedRecord Type
  | ExpectedRecordToHaveField Name Type
  | ExpectedForall Type
  | UnexpectedAdditionaArgs [Pat]
  | ExpectedArgOfType Type
  | InternalError
  | While Operation UnificationError
  | Where Context UnificationError
  deriving (Show) via PP UnificationError

data Operation
  = InferringType Prog
  | InferringKind Type
  | Deconstruct Type TDecl
  | Unifying Type Type

decorate :: (Unifies m) => Operation -> Sem m a -> Sem m a
decorate op act = do
  act `catch` (throw . While op)

die :: (Unifies m, HasContext m) => UnificationError -> Sem m a
die ue = do
  ctx <- ask
  throw (Where ctx ue)

instance Pretty Operation where
  pp = \case
    InferringType prog ->
      "inferring type of" `indent` pp prog

    InferringKind ty ->
      "inferring kind of" `indent` pp ty

    Deconstruct t td ->
      "deconstructing an argument" `indent` pp td
      `above` "out of" `indent` pp t

    Unifying l r -> do
      "unifying" `indent` pp l `above` "with" `indent` pp r

instance Pretty UnificationError where
  pp = \case
    Mismatch l r ->
      "Cannot match type"
        `indent` pp l
      `above` "with type"
        `indent` pp r

    Occurs n t ->
      "The name" |+| pp n
      `above` "is recursively defined as"
      `indent` pp t

    ExpectedRecord t ->
      "Expected the type"
        `indent` pp t
      `above` "to be a record"

    ExpectedRecordToHaveField n t ->
      "Expected the record"
        `indent` pp t
      `above` "to have field" |+| pp n

    ExpectedForall t ->
      "Expected the type"
        `indent` pp t
      `above` "to be a forall"

    UnexpectedAdditionaArgs pats ->
      "The pattern arguments" `indent` block pats `above` "are excessive"

    ExpectedArgOfType t -> do
      "Expecting another pattern argument of type" `indent` pp t

    InternalError ->
      "Internal error"

    While op err ->
      pp err `above` "while" `indent` pp op

    Where ctx err ->
      pp err `above` "where" `indent` pp ctx

unified :: (Unifies m, HasContext m) => Type -> Type -> Sem m Type
unified n m = decorate (Unifying n m) do
  n' <- applyBindings n
  m' <- applyBindings m
  unify n' m'
  applyBindings n'

unify :: (Unifies m, HasContext m) => Type -> Type -> Sem m ()
unify (TVar n) (TVar m)
  | n == m    = mempty
  | otherwise = modify (one n (TVar m) <>)

unify (TVar n) m
  | occurs n m = die $ Occurs n m
  | otherwise  = modify (one n m <>)

unify m (TVar n)
  | occurs n m = die $ Occurs n m
  | otherwise  = modify (one n m <>)

-- unify (TRigid t) (TRigid u)
--   | t == u = mempty

unify (TConst t) (TConst u)
  | t == u = mempty

unify (TApp a b) (TApp c d) = do
  unified a c
  unified b d
  return ()

unify (TArr c b) (TArr a d) = do
  unified a c
  unified b d
  return ()

unify (TRec ns) (TRec ms)
  | Just selection <- zipTDecls ms ns = do
    for_ selection \(l, r) -> do
      -- traceShowM (l, r)
      unified l r

unify (TFun n k t) (TFun m l u) = do
  unified k l
  v <- fresh n
  let t' = subst (one n (TRigid n)) t
  let u' = subst (one n (TRigid n)) u
  unified t' u'
  return ()

unify (TArr k t) (TFun m l u) = do
  unified k l
  n <- fresh "n"
  unified t (subst (one m (TVar n)) u)
  return ()

unify (TFun m l u) (TArr k t) = do
  unified k l
  n <- fresh "n"
  unified t (subst (one m (TVar n)) u)
  return ()

unify TStar TStar = mempty
unify n m = die $ Mismatch n m

zipTDecls :: [TDecl] -> [TDecl] -> Maybe [(Type, Type)]
zipTDecls ns ms = do
  let names = Set.fromList $ fmap tDeclName (ns ++ ms)
  for (Set.toList names) \name -> do
    tn <- findTDecl name ns
    tm <- findTDecl name ms
    return (tn, tm)

findTDecl :: Name -> [TDecl] -> Maybe Type
findTDecl n decls =
  case filter (tDeclHasName n) decls of
    _ ::= u : _ -> return u
    _           -> Nothing

tDeclHasName :: Name -> TDecl -> Bool
tDeclHasName n (m ::= _) = n == m
