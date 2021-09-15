{- | Type inference.
-}
module Infer1 where

import Control.Applicative (liftA2)
import Control.Monad (foldM)
import Control.Monad.Free
import Control.Arrow

import Data.Traversable (for)
import Data.Foldable (for_)

import Polysemy
-- import Polysemy.State (get)
import Polysemy.Error

import Name
import Prog1
import Context1
import Subst1
import Unify1
import Eval1
import Failure
import Pretty

import Debug.Trace

-- | Produce a program with some free variables bound and its type.
--
inference :: forall m. (Unifies m, HasContext m, HasFreshNames m) => Prog -> Sem m (Prog, Prog)
inference prog = do
  ty    <- infer prog
  prog' <- applyBindings prog
  return (prog', ty)

-- | The main inference procedure.
--
infer :: forall m. (Unifies m, HasContext m, HasFreshNames m) => Prog -> Sem m Prog
infer prog =
  decorate (InferringType prog) do
    --  traceShowM ("infer", prog)
    res <- case prog of
      Var   n -> Var <$> refresh n         -- Free vars are allowed to have any type.
      Rigid n -> find n                    -- Tound variables should exist in the context.

      Lam (Abstr n t b) -> do
        _ <- check t Star                  -- The arguments should have kind `Star`.
        let t' = eval t                    -- We reduce the type here, after tc;
                                           -- this way, eval shouldn't fail.
        tb <- withContext [(n, t')] do     -- We infer body under the binder.
          infer b

        return $ Pi $ Abstr n t' tb

      Pi (Abstr n t b) -> do
        _ <- check t Star
        let t' = eval t
        _ <- withContext [(n, t')] do
          infer b

        return $ Star

      Star -> return $ Star

      App f x -> do
        -- tf <- infer f
        -- tx <- infer x
        -- let r  = refresh "f"
        -- let n' = refresh "n"
        -- traceShowM (tf, (Pi (Abstr n' tx (Var r))))
        -- tf' <- unified tf (Pi (Abstr n' tx (Var r)))
        -- traceShowM (tf')
        -- case tf' of
        --   Pi (Abstr m u c) -> do
        --     traceShowM (instantiate m x c)
        --     applyBindings (instantiate m x c)

        --   _ -> error "how?"
        infer f >>= \case         -- I don't go usual `(?n : tx) -> ?r ~ tf` route
                                  -- because I can't make it work for a moment.
                                  -- so we will assume the function is a function here.
          Pi (Abstr n t b) -> do  -- TODO: fix.
            tx <- infer x
            _  <- unified t tx
            applyBindings (instantiate n x b)

          tf -> do
            die $ ExpectedForall tf

      Match o alts -> do
        t  <- infer o
        ts <- for alts $ inferAlt o           -- See `inferAlt`.
        r  <- refresh "r"
        foldM unified (Var r) ts

      Record ns -> do
        ds <- for ns \case
          Val n t b -> do
            tb <- infer b
            t' <- unified t tb
            return $ TDecl n t'

          Data {} -> error "data in record"  -- Because reasons.

        return $ Product ds

      Product ts -> do
        for_ ts \(TDecl n t) ->
          check t Star

        return Star

      Get p n -> do         -- We assume that object is already a record.
        infer p >>= \case   -- We don't have constraints, sadly.
          Product ds -> do
            case findTDecl n ds of
              Just t -> applyBindings t
              _      -> die $ ExpectedRecordToHaveField n (Product ds)

          other -> do
            die $ ExpectedRecord other

      LetRec ds b -> do                -- We just dump all stuff into the context,
        ns <- concat <$> for ds \case  -- it all will be inferred inside it.
          Val n t _ -> return [(n, t)]
          Data n args ctors -> do
            nts <- for ctors \(Ctor n' t) -> return [(n', telescope args t)]
            return $ (n, telescope args Star) : concat nts

        withContext ns do
          for_ ds \case
            Val n _ b' -> do
              t  <- find n
              t' <- infer b'
              unified (eval t) t'
              return ()

            -- No inference on datatypes, they are axioms.
            Data n args ctors -> do
              for_ ctors \case
                Ctor _ t -> do
                  -- We dump type arguments into the context, because they
                  -- are /bound/ in the @data@ declaration.
                  withContext [(n'', t'') | TDecl n'' t'' <- args] do
                    check (telescope args t) Star  -- check the resulting type
                    ret <- getCtorReturnType t
                    ctorCheckReturnType n args ret
                  return ()

          infer b

      Let d b -> do
        ns <- case d of
          Val n t b' -> do             -- We infer types before entering the ctx.
            tb <- infer b'
            t' <- unified (eval t) tb
            return [(n, t')]

          Data n args ctors -> do
            let k = telescope args Star
            nts <- for ctors \case
              Ctor n' t -> do
                let t' = telescope args t
                _ <- withContext ((n, k) : [(n'', t'') | TDecl n'' t'' <- args]) do
                  check t' Star
                  ret <- getCtorReturnType t
                  ctorCheckReturnType n args ret
                return [(n', t')]
            return $ (n, k) : concat nts

        withContext ns do
          infer b

      Lit   lit -> return $ inferLit lit
      Axiom _ t -> return t
      FFI   _ t -> return t
  --  traceShowM ("inferred", prog, "=>", res)
    return (eval res)

-- | Check that a program infers into given type. Return that type.
check :: forall m. (Unifies m, HasContext m, HasFreshNames m) => Prog -> Prog -> Sem m Prog
check p t = do
  t' <- infer p
  unified t' t

inferLit :: Literal -> Prog
inferLit I {} = Rigid "Integer"
inferLit F {} = Rigid "Float"
inferLit S {} = Rigid "String"

inferAlt :: (Unifies m, HasContext m, HasFreshNames m) => Prog -> Alt Prog -> Sem m Prog
inferAlt t (Alt pat body) = do
  delta <- match t pat  -- We turn the patten/(object type) into typing context here.
  withContext delta do
    infer body

match :: (Unifies m, HasContext m, HasFreshNames m) => Prog -> Pat -> Sem m [(Name, Prog)]
match t = \case
  PVar n -> return [(n, t)]
  PWild  -> return []
  PLit lit -> do
    unified t (inferLit lit)
    return []

  PRec pDecls -> do
    matchDecls t pDecls

  PCtor cName args -> do
    t'          <- find cName
    (ctx, tres) <- untelescope t' args  -- We deapply the constructor here.
    unified t tres                      -- Its formal args are matched with
    return ctx                          -- its real argument patterns.

matchDecls :: (Unifies m, HasContext m, HasFreshNames m) => Prog -> [PDecl] -> Sem m [(Name, Prog)]
matchDecls (Product decls) (PDecl n pat : rest) = do
    case findTDecl n decls of
      Just t  -> match t pat
      Nothing -> die $ ExpectedRecordToHaveField n (Product decls)
  <>
    matchDecls (Product decls) rest

matchDecls Product {} [] = mempty
matchDecls t _ = die $ ExpectedRecord t

untelescope :: (Unifies m, HasContext m, HasFreshNames m) => Prog -> [Pat] -> Sem m ([(Name, Prog)], Prog)
untelescope (Pi (Abstr _ k t)) (arg : rest) = do
  ctx         <- match k arg
  (ctxs, end) <- untelescope t rest
  return (ctx <> ctxs, end)

untelescope (Pi (Abstr _ k _)) _ = die $ ExpectedArgOfType k

untelescope t []   = return ([], t)
untelescope _ args = die $ UnexpectedAdditionaArgs args

-- Lazy in the monoidal accumulator.
foldlForM :: forall g b a m. (Foldable g, Monoid b, Applicative m) => g a -> (a -> m b) -> m b
foldlForM xs f = foldr f' (pure mempty) xs
  where
  f' :: a -> m b -> m b
  f' x y = liftA2 mappend (f x) y

-- instantiate :: (Unifies m) => Prog -> Sem m Prog
-- instantiate (TFun n _ b) = do
--   n' <- fresh n
--   instantiate $ subst (one n (TVar n')) b

-- instantiate t = return t

getCtorReturnType :: (Unifies m, HasContext m, HasFreshNames m) => Prog -> Sem m Prog
getCtorReturnType (Pi (Abstr n _ r)) = do
  n' <- refresh n
  getCtorReturnType $ subst (Bound n ==> Var n') r
getCtorReturnType other = return other

-- | Check that constructor of `List a` returns `List a`.
--
ctorCheckReturnType :: forall m. (Unifies m, HasContext m, HasFreshNames m) => Name -> [TDecl Prog] -> Prog -> Sem m ()
ctorCheckReturnType tName args checked = go checked (reverse args)
  where
    go :: Prog -> [TDecl Prog] -> Sem m ()
    go t [] = do
      _ <- unified (Rigid tName) t
      return ()

    go t@(App f x) (td@(TDecl _ k) : rest) = decorate (Deconstruct t td) do
      t' <- infer x
      _  <- unified t' k
      go f rest

    go _ _ = die InternalError -- TODO: Not just die here, produce a message.
