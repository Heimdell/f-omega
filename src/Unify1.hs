
module Unify1 where

import Control.Monad.Free

import Data.Set qualified as Set
import Data.Traversable
import Data.Foldable

import Polysemy
import Polysemy.Error
import Polysemy.State hiding (Get)
import Polysemy.Reader

import Name
import Prog1
import Fresh
import Subst1
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
  = Mismatch Prog Prog
  | Occurs Name Prog
  | ExpectedRecord Prog
  | ExpectedRecordToHaveField Name Prog
  | ExpectedForall Prog
  | UnexpectedAdditionaArgs [Pat]
  | ExpectedArgOfType Prog
  | InternalError
  | While Operation UnificationError
  | Where Context UnificationError
  deriving (Show) via PP UnificationError

data Operation
  = InferringType Prog
  | InferringKind Prog
  | Deconstruct Prog (TDecl Prog)
  | Unifying Prog Prog

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

unified :: (Unifies m, HasContext m) => Prog -> Prog -> Sem m Prog
unified n m = decorate (Unifying n m) do
  n' <- applyBindings n
  m' <- applyBindings m
  unify n' m'
  applyBindings n'

-- | TODO: Check if in (Bound n ~ FreeVar a) the `a` is above `n` in context.
--
class Unify a where
  unify :: (Unifies m, HasContext m) => a -> a -> Sem m ()

instance Unify Prog where
  unify (Pure (FreeVar n)) (Pure (FreeVar m))
    | n == m    = mempty
    | otherwise = modify (FreeVar n ==> (Pure (FreeVar m)) <>)

  unify (Pure (FreeVar n)) m
    | occurs n m = die $ Occurs n m
    | otherwise  = modify (FreeVar n ==> m <>)

  unify m (Pure (FreeVar n))
    | occurs n m = die $ Occurs n m
    | otherwise  = modify (FreeVar n ==> m <>)

  unify (Free (App a b)) (Free (App c d)) = do
    unify a c
    unify b d

  unify (Free (Pi  a)) (Free (Pi  b)) = unify a b
  unify (Free (Lam a)) (Free (Lam b)) = unify a b
  unify (Free Star)    (Free Star)    = return ()

  unify (Free (Record ds)) (Free (Record gs)) = do
    case zipDecls ds gs of
      Just quads -> for_ quads \(tn, tm, n, m) -> do
        unify tn tm
        unify  n  m

      Nothing -> do
        die $ Mismatch (Free (Record ds)) (Free (Record gs))

  unify (Free (TRec tds)) (Free (TRec tgs)) = do
    case zipTDecls tds tgs of
      Just pairs -> for_ pairs \(n, m) -> do
        unify n m

      Nothing -> do
        die $ Mismatch (Free (TRec tds)) (Free (TRec tgs))

  unify (Pure (Bound t))   (Pure (Bound u))   | t == u = mempty
  unify (Free (Lit   l))   (Free (Lit   k))   | l == k = mempty
  unify (Free (Axiom n _)) (Free (Axiom m _)) | n == m = mempty
  unify (Free (FFI   n _)) (Free (FFI   m _)) | n == m = mempty

  unify a@(Free Match {}) _ = notNormalisedError a
  unify _ a@(Free Match {}) = notNormalisedError a

  unify a@(Free Get {}) _ = notNormalisedError a
  unify _ a@(Free Get {}) = notNormalisedError a

  unify a@(Free Let {}) _ = notNormalisedError a
  unify _ a@(Free Let {}) = notNormalisedError a

  unify a@(Free LetRec {}) _ = notNormalisedError a
  unify _ a@(Free LetRec {}) = notNormalisedError a

  unify a b = die $ Mismatch a b

notNormalisedError :: Prog -> a
notNormalisedError a = error $ "There term for unification is not normalised: " ++ show (pp a)

instance Unify (Abstr Prog) where
  unify (Abstr n t b) (Abstr m u c) = do
    unify t u
    unify b (subst (Bound m ==> Pure (Bound n)) c)

zipTDecls :: [TDecl Prog] -> [TDecl Prog] -> Maybe [(Prog, Prog)]
zipTDecls ns ms = do
  let names = Set.fromList $ fmap tDeclName (ns ++ ms)
  for (Set.toList names) \name -> do
    tn <- findTDecl name ns
    tm <- findTDecl name ms
    return (tn, tm)

zipDecls :: [Decl r Prog] -> [Decl r Prog] -> Maybe [(Prog, Prog, Prog, Prog)]
zipDecls ns ms = do
  let names = Set.fromList $ declName =<< (ns ++ ms)
  for (Set.toList names) \name -> do
    (tn, n) <- findDecl name ns
    (tm, m) <- findDecl name ms
    return (tn, tm, n, m)

findTDecl :: Name -> [TDecl Prog] -> Maybe Prog
findTDecl n decls =
  case filter (tDeclHasName n) decls of
    TDecl _ u : _ -> return u
    _             -> Nothing

tDeclHasName :: Name -> TDecl Prog -> Bool
tDeclHasName n (TDecl m _) = n == m

declName :: Decl r Prog -> [Name]
declName = \case
  Val  n _ _     -> [n]
  Data n _ ctors -> n : [n' | Ctor n' _ <- ctors]

findDecl :: Name -> [Decl r Prog] -> Maybe (Prog, Prog)
findDecl n ((>>= asVals) -> decls) =
  case filter (\(n', _) -> n == n') decls of
    ((_, p) : _) -> Just p
    _            -> Nothing

asVals :: Decl r Prog -> [(Name, (Prog, Prog))]
asVals = \case
  Val  n t   b     -> [(n, (t, b))]
  Data n tas ctors ->
      (n, (telescope tas (Free Star), Free Star))
    : [(n', (t, Free Star)) | Ctor n' t <- ctors]

telescope :: [TDecl Prog] -> Prog -> Prog
telescope tas b = foldr makePi b tas
  where
    makePi (TDecl n t) b' = Free $ Pi $ Abstr n t b'
