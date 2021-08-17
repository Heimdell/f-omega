
module Infer where

import Data.Traversable (for)
import Data.Foldable (for_)

import Polysemy
-- import Polysemy.State (get)
import Polysemy.Error

import Name
import Prog
import Fresh
import Context
import Subst
import Unify
import Pretty

import Debug.Trace

inference :: forall m. (Unifies m, HasContext m) => Prog -> Sem m HasType
inference prog = do
  ty    <- infer prog
  prog' <- applyBindings prog
  return $ HasType (prog', ty)

newtype HasType = HasType (Prog, Type)
  deriving (Show) via PP HasType

instance Pretty HasType where
  pp (HasType (prog, ty)) =
    pp prog
    `indent` "::" |+| pp ty

infer :: forall m. (Unifies m, HasContext m) => Prog -> Sem m Type
infer prog = decorate (InferringType prog) do
  -- traceShowM ("infer", prog)
  case prog of
    Var n -> find n
    Sym n -> find n
    Lam n t b -> do
      withContext [(n, t)] do
        tb <- infer b
        applyBindings $ TArr t tb

    App f x -> do
      -- traceShowM ("infer app", f, x)
      tf  <- infer f
      -- traceShowM ("tf", tf)
      tf' <- instantiate tf
      tx  <- infer x
      tx'' <- case (tf', tx) of
        (TArr TFun {} _, TFun {}) -> return tx
        (_,              TFun {}) -> instantiate tx
        _                         -> return tx

      r   <- fresh "r"
      _   <- unified tf' (TArr tx'' (TVar r))
      applyBindings (TVar r)

    LAM n k b -> do
      withContext [(n, k)] do
        tb <- infer b
        applyBindings $ TFun n k tb

    APP f t -> do
      tf  <- infer f
      kt  <- inferKind t
      case tf of
        TFun n k b -> do
          _ <- unified k kt
          applyBindings (subst (one n t) b)

        other -> do
          die $ ExpectedForall other

    Rec ns -> do
      ds <- for ns \case
        Val n t b -> do
          tb <- infer b
          t' <- unified t tb
          return $ n ::= t'

        Capture n -> do
          t  <- find n
          t' <- applyBindings t
          return $ n ::= t'

        Data {} -> error "data in record"

      return $ TRec ds

    Get p n -> do
      infer p >>= \case
        TRec ds -> do
          case findName n ds of
            Just t -> applyBindings t
            _      -> die $ ExpectedRecordToHaveField n (TRec ds)

        other -> do
          die $ ExpectedRecord other

    Lit I {} -> return $ TConst "Integer"
    Lit F {} -> return $ TConst "Float"
    Lit S {} -> return $ TConst "String"

    LetRec ds b -> do
      ns <- concat <$> for ds \case
        Capture {} -> error "capture in let"

        Val n t _ -> do
          return [(n, t)]

        Data n args ctors -> do
          k   <- telescope args TStar
          nts <- for ctors \case
            Ctor n' t -> do
              t' <- telescope args t
              return [(n', t')]
          return $ (n, k) : concat nts

      withContext ns do
        for_ ds \case
          Capture {} -> error "okay"
          Val n _ b' -> do
            t  <- find n
            t' <- infer b'
            -- traceShowM (t, t')
            -- traceShowM =<< get @Subst
            unified t t'
            -- traceShowM =<< get @Subst
            return ()

          -- No inference on datatypes, they are axioms.
          Data {} -> do
            return ()

        infer b

    Let d b -> do
      ns <- case d of
        Val n t b' -> do
          tb <- infer b'
          t' <- unified t tb
          return [(n, t')]

        Data n args ctors -> do
          k   <- telescope args TStar
          nts <- for ctors \case
            Ctor n' t -> do
              t' <- telescope args t
              ret <- getCtorReturnType t
              ctorCheckReturnType n args ret
              _ <- withContext ((n, k) : [(n, t) | n ::= t <- args]) do
                inferKind t'
              return [(n', t')]
          return $ (n, k) : concat nts

        Capture {} -> error "capture in let"

      -- traceShowM ("let context", ns)
      withContext ns do
        infer b

instantiate :: (Unifies m) => Type -> Sem m Type
instantiate (TFun n k b) = do
  n' <- fresh n
  instantiate $ subst (one n (TVar n')) b

instantiate t = return t

getCtorReturnType :: (Unifies m, HasContext m) => Type -> Sem m Type
getCtorReturnType (TArr _ r) = getCtorReturnType r
getCtorReturnType (TFun n _ r) = do
  n' <- fresh n
  getCtorReturnType (subst (one n (TVar n')) r)
getCtorReturnType other = return other

ctorCheckReturnType :: forall m. (Unifies m, HasContext m) => Name -> [TDecl] -> Type -> Sem m ()
ctorCheckReturnType tName args checked = go checked (reverse args)
  where
    go :: Type -> [TDecl] -> Sem m ()
    go t [] = do
      _ <- unified (TConst tName) t
      return ()

    go t@(TApp f x) (td@(n ::= k) : rest) = decorate (Deconstruct t td) do
      t' <- inferKind x
      _  <- unified t' k
      go f rest

    go t _ = die InternalError


telescope :: Unifies m => [TDecl] -> Type -> Sem m Type
telescope args end = applyBindings (foldr go end args)
  where
    go (n ::= t) b = TFun n t b

inferKind :: (Unifies m, HasContext m) => Type -> Sem m Type
inferKind ty = decorate (InferringKind ty) do
  -- traceShowM ("inferKind", ty)
  k <- case ty of
    TVar   n -> find n `catch` \(_ :: ContextError) -> (TVar <$> fresh "k")
    TConst n -> find n
    TApp f x -> do
      kf <- inferKind f
      kx <- inferKind x
      r  <- fresh "r"
      _  <- unified kf (TArr kx (TVar r))
      applyBindings (TVar r)

    TArr d c -> do
      _ <- inferKind d
      _ <- inferKind c
      return TStar

    TRec ds -> do
      for ds \(_ ::= t) -> do
        unified t TStar
      return TStar

    TFun _ k t -> do
      _  <- inferKind k
      kt <- inferKind t
      applyBindings $ TArr k kt

    TStar -> return TStar
  -- traceShowM ("inferKind", ty, "=", k)
  return k

test :: Prog -> Either ContextError (Either UnificationError HasType)
test prog
  = run
  $ runContext
  $ runFresh
  $ evalUnification
  $ inference
  $ prog

prog2 :: Prog
prog2
  = Let (Val "id" "tid" $ LAM "a" TStar $ Lam "b" "a" "b")
  $ "id" `App` Lit (I 1)

prog1 :: Prog
prog1
  = App (Lam "a" (TRec ["a" ::= "Integer", "b" ::= "String"])
        $ Get "a" "a")

        (Rec
          [ Val "a" "ta" $ Lit (I 1)
          , Val "b" "tb" $ Lit $ S "2"
          ])

prog3 :: Prog
prog3 =
  Let (Data "List" ["a" ::= TStar]
    [ Ctor "Nil" $ TApp "List" "a"
    , Ctor "Cons" $ "a" `TArr` (TApp "List" "a" `TArr` TApp "List" "a")
    ])
  $ ("Cons" `App` Lit (I 1)) `App` "Nil"

prog4 :: Prog
prog4 =
  Let (Data "Free" ["f" ::= (TStar `TArr` TStar), "a" ::= TStar]
    [ Ctor "Pure" $ "a" `TArr` (TApp "Free" "f" `TApp` "a")
    , Ctor "Join" $ ("f" `TApp` (("Free" `TApp` "f") `TApp` "a")) `TArr` (("Free" `TApp` "f") `TApp` "a")
    ])
  $ Let (Data "List" ["a" ::= TStar]
    [ Ctor "Nil" $ TApp "List" "a"
    , Ctor "Cons" $ "a" `TArr` (TApp "List" "a" `TArr` TApp "List" "a")
    ])
  $ "Join" `App` (("Cons" `App` ("Pure" `App` Lit (I 1))) `App` "Nil")
