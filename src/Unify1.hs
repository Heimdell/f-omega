
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
import Subst1
import Pretty
import Context1
import Failure

import Debug.Trace qualified as Debug

type Unifies m =
  ( Members '[Error Failure, State Subst] m
  )

evalUnification
  :: forall m a
  .  Sem (Error Failure : State Subst : m) a
  -> Sem m (Either Failure a)
evalUnification = evalState mempty . runError

runUnification
  :: forall m a
  .  Sem (Error Failure : State Subst : m) a
  -> Sem m (Subst, Either Failure a)
runUnification = runState mempty . runError

applyBindings :: (Unifies m, Substitutable t) => t -> Sem m t
applyBindings t = do
  s <- get @Subst
  return (subst s t)

decorate :: (Unifies m) => Operation -> Sem m a -> Sem m a
decorate op act = do
  act `catch` (throw . While op)

die :: (Unifies m, HasContext m) => Failure -> Sem m a
die ue = do
  Context ctx <- ask
  throw (Where ctx ue)

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
  unify (Var n) (Var m)
    | n == m    = mempty
    | otherwise = modify (FreeVar n ==> (Var m) <>)

  unify (Var n) m
    | occurs n m = die $ Occurs n m
    | otherwise  = modify (FreeVar n ==> m <>)

  unify m (Var n)
    | occurs n m = die $ Occurs n m
    | otherwise  = modify (FreeVar n ==> m <>)

  unify (App a b) (App c d) = do
    unify a c
    unify b d

  unify (Pi  a) (Pi  b) = unify a b
  unify (Lam a) (Lam b) = unify a b
  unify  Star    Star   = return ()

  unify (Record ds) (Record gs) = do
    case zipDecls ds gs of
      Just quads -> for_ quads \(tn, tm, n, m) -> do
        unify tn tm
        unify  n  m

      Nothing -> do
        die $ Mismatch (Record ds) (Record gs)

  unify (Product tds) (Product tgs) = do
    case zipTDecls tds tgs of
      Just pairs -> for_ pairs \(n, m) -> do
        unify n m

      Nothing -> do
        die $ Mismatch (Product tds) (Product tgs)

  unify (Rigid t)   (Rigid u)   | t == u = mempty
  unify (Lit   l)   (Lit   k)  | l == k = mempty
  unify (Axiom n _) (Axiom m _) | n == m = mempty
  unify (FFI   n _) (FFI   m _) | n == m = mempty

  unify a@Match {} _ = notNormalisedError a
  unify _ a@Match {} = notNormalisedError a

  unify a@Get {} _ = notNormalisedError a
  unify _ a@Get {} = notNormalisedError a

  unify a@Let {} _ = notNormalisedError a
  unify _ a@Let {} = notNormalisedError a

  unify a@LetRec {} _ = notNormalisedError a
  unify _ a@LetRec {} = notNormalisedError a

  unify a b = die $ Mismatch a b

notNormalisedError :: Prog -> a
notNormalisedError a = error $ "There term for unification is not normalised: " ++ show (pp a)

instance Unify (Abstr Prog) where
  unify (Abstr n t b) (Abstr m u c) = do
    unify t u
    unify b (subst (Bound m ==> Rigid n) c)

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
      (n, (telescope tas Star, Star))
    : [(n', (t, Star)) | Ctor n' t <- ctors]
