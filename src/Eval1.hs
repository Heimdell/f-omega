
{- | Normalisation, used in inference to reduce type expressions.
-}

module Eval1 (Evals, eval) where

import Control.Monad.Free
-- import Control.Applicative (empty)

import Data.Maybe
import Data.Monoid (First (..))

import Name
import Prog1
import Subst1

class Evals a where
  eval :: a -> a

instance Evals Prog where
  -- Anything we can't eval it left as-is.
  eval prog = case prog of
    Var   n   -> Var n             -- vars are evaluated to themselves
    Rigid n   -> Rigid n           -- -"-
    Lam abstr -> Lam $ eval abstr  -- we perform redunctions for both lambdas
    Pi  abstr -> Pi  $ eval abstr  -- and pi-types

    Star      -> Star

    Record decls -> Record $ map eval decls

    App f x -> case (eval f, eval x) of
      -- we don't eval types here, because they were evaluated by type checker
      (Lam (Abstr n _ body), x') -> eval $ instantiate n x' body
      (f', x') -> App f' x'

    Get o field -> case eval o of
      Record decls -> find field decls
      o'           -> Get o' field

    Match o alts -> do
      let o'    = eval o
      let alts' = map eval alts
      match o' alts'

    Product tDecls -> do
      Product $ map eval tDecls

    Let val b -> do
      let val' = eval val
      let b'   = eval b
      let s    = asSubst val'
      eval $ subst s b'

    fixpoint@LetRec {} -> do
      -- They also not evaluated in general yet T_T (but typechecked).
      error $ "fixpoints in normalization-time exressions are not yet supported: " ++ show fixpoint

    Lit   l   -> Lit l
    Axiom n t -> Axiom n t
    FFI   n t -> FFI n t

instance Evals (Decl r Prog) where
  eval = \case
    Val  n ty  b     -> Val  n     (eval ty)      (eval b)
    Data n tys ctors -> Data n (map eval tys) (map eval ctors)

instance Evals (Abstr Prog) where eval (Abstr n ty b) = Abstr n (eval ty) (eval b)
instance Evals (Alt   Prog) where eval (Alt   p b)    = Alt   p (eval b)
instance Evals (TDecl Prog) where eval (TDecl n t)    = TDecl n (eval t)
instance Evals (Ctor  Prog) where eval (Ctor  n t)    = Ctor  n (eval t)

-- | Locate a name in a set of declarations.
--
--   Produces an "axiom" if name refers to a constructor or datatype.
--
find :: Name -> [Decl r Prog] -> Prog
find n (Val  n' _ p                : _) | n == n' = p
find n (Data n' tas _              : _) | n == n' = Axiom n' (telescope tas Star)
find n (Data _  _ (Ctor n' t : _)  : _) | n == n' = Axiom n' t
find n (Data n' t (_         : cs) : r) | n == n' = find n $ Data n' t cs : r
find n (_ : rest)                                 = find n rest
find n []                                         = error $ "find " ++ show n

-- | Pattern match evaluator.
--
match :: Prog -> [Alt Prog] -> Prog
match prog'1 alts = fromMaybe (Match prog'1 alts) $ getFirst $ foldMap (matchOne prog'1) alts
  where
    matchOne prog (Alt pat body) = do
      s <- matchPat prog pat
      return $ eval $ subst s body

    matchPat prog' pat = case (prog', pat) of
      (prog,      PVar n)                -> return (Bound n ==> prog)
      (Axiom n _, PCtor n' []) | n == n' -> return mempty
      (App   f x, PCtor n' args)
        | px : _ <- reverse args ->
          matchPat f (PCtor n' (init args)) <> matchPat x px

      (Record {},    PRec [])                      -> return mempty
      (Record decls, PRec (PDecl n pat' : pdecls)) -> do
        let p = find n decls
        matchPat p pat' <> matchPat (Record decls) (PRec pdecls)

      (_,     PWild)             -> return mempty
      (Lit l, PLit l') | l == l' -> return mempty

      _ -> mempty

asSubst :: Decl 'NonRec Prog -> Subst
asSubst = \case
  Val  n _   b     -> Bound n ==> b
  Data n tas ctors -> axiom n (telescope tas Star) <> mconcat [axiom n' t | Ctor n' t <- ctors]
