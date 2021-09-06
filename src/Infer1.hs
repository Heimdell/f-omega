
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

inference :: forall m. (Unifies m, HasContext m) => Prog -> Sem m (Prog, Prog)
inference prog = do
  ty    <- infer prog
  prog' <- applyBindings prog
  return (prog', ty)

infer :: forall m. (Unifies m, HasContext m) => Prog -> Sem m Prog
infer prog = fmap eval $ decorate (InferringType prog) case prog of
  Var   n -> return $ Var (refresh n)
  Rigid n -> find n

  Lam (Abstr n t b) -> do
    _ <- check t Star
    let t' = eval t
    tb <- withContext [(n, t')] do
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
    tf <- infer f
    tx <- infer x
    let r = refresh "r"
    unify tf $ Pi $ Abstr (refresh "n") tx (Var r)
    applyBindings (Var r)

  Match o alts -> do
    t  <- infer o
    ts <- for alts $ inferAlt o
    foldM unified (Var (refresh "r")) ts

  Record ns -> do
    ds <- for ns \case
      Val n t b -> do
        tb <- infer b
        t' <- unified t tb
        return $ TDecl n t'

      Data {} -> error "data in record"

    return $ Product ds

  Product ts -> do
    for_ ts \(TDecl n t) ->
      check t Star

    return Star

  Get p n -> do
    infer p >>= \case
      Product ds -> do
        case findTDecl n ds of
          Just t -> applyBindings t
          _      -> die $ ExpectedRecordToHaveField n (Product ds)

      other -> do
        die $ ExpectedRecord other

  LetRec ds b -> do
    ns <- concat <$> for ds \case
      Val n t _ -> return [(n, eval t)]

      Data n args ctors -> do
        nts <- for ctors \(Ctor n' t) -> do
          return [(n', telescope args t)]

        return $ (n, telescope args Star) : concat nts

    withContext ns do
      for_ ds \case
        Val n _ b' -> do
          t  <- find n
          t' <- infer b'
          unified t t'
          return ()

        -- No inference on datatypes, they are axioms.
        Data n args ctors -> do
          for_ ctors \case
            Ctor _ t -> do
              withContext [(n'', t'') | TDecl n'' t'' <- args] do
                check (telescope args t) Star
                ret <- getCtorReturnType t
                ctorCheckReturnType n args ret
              return ()

      infer b

  Let d b -> do
    ns <- case d of
      Val n t b' -> do
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

check :: forall m. (Unifies m, HasContext m) => Prog -> Prog -> Sem m Prog
check p t = do
  t' <- infer p
  unified t' t

inferLit :: Literal -> Prog
inferLit I {} = Rigid "Integer"
inferLit F {} = Rigid "Float"
inferLit S {} = Rigid "String"

inferAlt :: (Unifies m, HasContext m) => Prog -> Alt Prog -> Sem m Prog
inferAlt t (Alt pat body) = do
  delta <- match t pat
  withContext delta do
    infer body

match :: (Unifies m, HasContext m) => Prog -> Pat -> Sem m [(Name, Prog)]
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
    (ctx, tres) <- untelescope t' args
    unified t tres
    return ctx

  -- PType t' -> do
  --   unified t t'
  --   return []

matchDecls :: (Unifies m, HasContext m) => Prog -> [PDecl] -> Sem m [(Name, Prog)]
matchDecls (Product decls) (PDecl n pat : rest) = do
    case findTDecl n decls of
      Just t  -> match t pat
      Nothing -> die $ ExpectedRecordToHaveField n (Product decls)
  <>
    matchDecls (Product decls) rest

matchDecls Product {} [] = mempty
matchDecls t _ = die $ ExpectedRecord t

untelescope :: (Unifies m, HasContext m) => Prog -> [Pat] -> Sem m ([(Name, Prog)], Prog)
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

getCtorReturnType :: (Unifies m, HasContext m) => Prog -> Sem m Prog
getCtorReturnType (Pi (Abstr n _ r)) = do
  getCtorReturnType $ subst (Bound n ==> Var (refresh n)) r
getCtorReturnType other = return other

ctorCheckReturnType :: forall m. (Unifies m, HasContext m) => Name -> [TDecl Prog] -> Prog -> Sem m ()
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

    go _ _ = die InternalError

-- telescope :: Unifies m => [TDecl] -> Prog -> Sem m Prog
-- telescope args end = applyBindings (foldr go end args)
--   where
--     go (n ::= t) b = TFun n t b

-- inferKind :: (Unifies m, HasContext m) => Prog -> Sem m Prog
-- inferKind ty = decorate (InferringKind ty) do
--   -- traceShowM ("inferKind", ty)
--   k <- case ty of
--     TVar   n -> find n `catch` \(_ :: ContextError) -> (TVar <$> fresh "k")
--     TRigid n -> find n `catch` \(_ :: ContextError) -> (TVar <$> fresh "k")
--     TConst n -> find n
--     TApp f x -> do
--       kf <- inferKind f
--       kx <- inferKind x
--       r  <- fresh "r"
--       _  <- unified kf (TArr kx (TVar r))
--       applyBindings (TVar r)

--     TArr d c -> do
--       _ <- inferKind d
--       _ <- inferKind c
--       return TStar

--     Product ds -> do
--       for ds \(_ ::= t) -> do
--         unified t TStar
--       return TStar

--     TFun _ k t -> do
--       _  <- inferKind k
--       kt <- inferKind t
--       applyBindings $ TArr k kt

--     TStar -> return TStar
--   -- traceShowM ("inferKind", ty, "=", k)
--   return k

-- test :: Prog -> Either ContextError (Either UnificationError HasType)
-- test prog
--   = run
--   $ runContext
--   $ runFresh
--   $ evalUnification
--   $ inference
--   $ prog

-- prog2 :: Prog
-- prog2
--   = Let (Val "id" "tid" $ LAM "a" TStar $ Lam "b" "a" "b")
--   $ "id" `App` Lit (I 1)

-- prog1 :: Prog
-- prog1
--   = App (Lam "a" (Product ["a" ::= "Integer", "b" ::= "String"])
--         $ Get "a" "a")

--         (Rec
--           [ Val "a" "ta" $ Lit (I 1)
--           , Val "b" "tb" $ Lit $ S "2"
--           ])

-- prog3 :: Prog
-- prog3 =
--   Let (Data "List" ["a" ::= TStar]
--     [ Ctor "Nil" $ TApp "List" "a"
--     , Ctor "Cons" $ "a" `TArr` (TApp "List" "a" `TArr` TApp "List" "a")
--     ])
--   $ ("Cons" `App` Lit (I 1)) `App` "Nil"

-- prog4 :: Prog
-- prog4 =
--   LetRec
--     [ Data "Free" ["f" ::= (TStar `TArr` TStar), "a" ::= TStar]
--       [ Ctor "Pure" $ "a" `TArr` (TApp "Free" "f" `TApp` "a")
--       , Ctor "Join" $ ("f" `TApp` (("Free" `TApp` "f") `TApp` "a")) `TArr` (("Free" `TApp` "f") `TApp` "a")
--       ]
--     , Data "List" ["a" ::= TStar]
--       [ Ctor "Nil" $ TApp "List" "a"
--       , Ctor "Cons" $ "a" `TArr` (TApp "List" "a" `TArr` TApp "List" "a")
--       ]
--     ]
--   $ "Join" `App` (("Cons" `App` ("Pure" `App` Lit (I 1))) `App` "Nil")

-- prog5 :: Prog
-- prog5 =
--   Let (Data "List" ["a" ::= TStar]
--     [ Ctor "Nil" $ TApp "List" "a"
--     , Ctor "Cons" $ "a" `TArr` (TApp "List" "a" `TArr` TApp "List" "a")
--     ])
--   $ LetRec
--     [ Data "Tree" ["a" ::= TStar]
--       [ Ctor "MkTree" $ "a" `TArr` (TApp "Forest" "a" `TArr` TApp "Tree" "a")
--       ]
--     , Data "Forest" ["a" ::= TStar]
--       [ Ctor "MkForest" $ TApp "List" (TApp "Tree" "a") `TArr` TApp "Forest" "a"
--       ]
--     ]
--   $ "MkForest" `App` (("Cons" `App` (("MkTree" `App` LAM "n" TStar (Lam "m" "n" "m")) `App` ("MkForest" `App` "Nil"))) `App` "Nil")
