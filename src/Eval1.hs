
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
  eval (Pure n) = Pure n
  eval (Free prog) = case prog of
    Lam abstr -> Free $ Lam $ eval abstr
    Pi  abstr -> Free $ Pi  $ eval abstr

    Star      -> Free Star

    Record decls -> Free $ Record $ map eval decls

    App f x -> case (eval f, eval x) of
      -- we don't eval types here, because they were evaluated by type checker
      (Free (Lam (Abstr n _ body)), x') -> eval $ instantiate n x' body
      (f', x') -> Free $ App f' x'

    Get o field -> case eval o of
      Free (Record decls) -> find field decls
      o'                  -> Free $ Get o' field

    Match o alts -> do
      let o'    = eval o
      let alts' = map eval alts
      match o' alts'

    TRec tDecls -> do
      Free $ TRec $ map eval tDecls

    Let val b -> do
      let val' = eval val
      let b'   = eval b
      let s    = asSubst val'
      eval $ subst s b'

    fixpoint@LetRec {} -> do
      error $ "fixpoints in normalization-time exressions are not yet supported: " ++ show fixpoint

    Lit   l   -> Free $ Lit l
    Axiom n t -> Free $ Axiom n t

instance Evals (Decl r Prog) where
  eval = \case
    Val  n ty  b     -> Val  n     (eval ty)      (eval b)
    Data n tys ctors -> Data n (map eval tys) (map eval ctors)

instance Evals (Abstr Prog) where eval (Abstr n ty b) = Abstr n (eval ty) (eval b)
instance Evals (Alt   Prog) where eval (Alt   p b)    = Alt   p (eval b)
instance Evals (TDecl Prog) where eval (TDecl n t)    = TDecl n (eval t)
instance Evals (Ctor  Prog) where eval (Ctor  n t)    = Ctor  n (eval t)

find :: Name -> [Decl r Prog] -> Prog
find n (Val  n' _ p                : _) | n == n' = p
find n (Data n' _  _               : _) | n == n' = Free $ Axiom n' (Free Star)
find n (Data _  _ (Ctor n' t : _)  : _) | n == n' = Free $ Axiom n' t
find n (Data n' t (_         : cs) : r) | n == n' = find n $ Data n' t cs : r
find n (_ : rest)                                 = find n rest
find n []                                         = error $ "find " ++ show n

match :: Prog -> [Alt Prog] -> Prog
match prog'1 alts = fromMaybe (Free $ Match prog'1 alts) $ getFirst $ foldMap (matchOne prog'1) alts
  where
    matchOne prog (Alt pat body) = do
      s <- matchPat prog pat
      return $ eval $ subst s body

    matchPat prog' pat = case (prog', pat) of
      (prog,             PVar n)                -> return (Bound n ==> prog)
      (Free (Axiom n _), PCtor n' []) | n == n' -> return mempty
      (Free (App   f x), PCtor n' args)
        | px : _ <- reverse args ->
          matchPat f (PCtor n' (init args)) <> matchPat x px

      (Free  Record {},     PRec [])                      -> return mempty
      (Free (Record decls), PRec (PDecl n pat' : pdecls)) -> do
        let p = find n decls
        matchPat p pat' <> matchPat (Free (Record decls)) (PRec pdecls)

      (_,            PWild)             -> return mempty
      (Free (Lit l), PLit l') | l == l' -> return mempty

      _ -> mempty

asSubst :: Decl 'NonRec Prog -> Subst
asSubst = \case
  Val  n _ b     -> Bound n ==> b
  Data n _ ctors -> axiom n (Free Star) <> mconcat [axiom n' t | Ctor n' t <- ctors]
