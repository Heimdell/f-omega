
module Eval1 where

import Control.Monad.Free
import Control.Applicative (empty)

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
      (Free (Lam (Abstr n ty body)), x') -> eval $ instantiate n x' body
      (f', x') -> Free $ App f' x'

    Get o field -> case eval o of
      Free (Record decls) -> find field decls

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
      eval $ subst s b

    LetRec decls b -> do

    Lit   l -> Free $ Lit l
    Axiom n -> Free $ Axiom n

instance Evals (Abstr Prog) where
  eval (Abstr n ty b) =
    Abstr n (eval ty) (eval b)

instance Evals (Decl r Prog) where
  eval (Val n ty b) =
    Val n (eval ty) (eval b)

instance Evals (Alt Prog) where
  eval (Alt pat b) =
    Alt pat (eval b)

instance Evals (TDecl Prog) where
  eval (TDecl n t) =
    TDecl n (eval t)

find :: Name -> [Decl r Prog] -> Prog
find n (Val  n' _ p                : _) | n == n' = p
find n (Data n' _  _               : _) | n == n' = Free $ Axiom n'
find n (Data _  _ (Ctor n' _ : _)  : _) | n == n' = Free $ Axiom n'
find n (Data n' t (_         : cs) : r) | n == n' = find n $ Data n' t cs : r
find n (_ : rest)                                 = find n rest
find n []                                         = error $ "find " ++ show n

match :: Prog -> [Alt Prog] -> Prog
match prog alts = fromMaybe (Free $ Match prog alts) $ getFirst $ foldMap (matchOne prog) alts
  where
    matchOne prog (Alt pat body) = do
      s <- matchPat prog pat
      return $ eval $ subst s body

    matchPat prog pat = case (prog, pat) of
      (prog,           PVar n)                -> return (Bound n ==> prog)
      (Free (Axiom n), PCtor n' []) | n == n' -> return mempty
      (Free (App f x), PCtor n' args)
        | px : _ <- reverse args ->
          matchPat f (PCtor n' (init args)) <> matchPat x px

      (Free Record {}, PRec []) -> return mempty
      (Free (Record decls), PRec (PDecl n pat : pdecls)) -> do
        let p = find n decls
        matchPat p pat <> matchPat (Free (Record decls)) (PRec pdecls)

      (_, PWild) -> return mempty
      (Free (Lit l), PLit l') | l == l' -> return mempty

      _ -> mempty

asSubst :: Decl 'NonRec Prog -> Subst
asSubst = \case
  Val  n _ b     -> Bound n ==> b
  Data n _ ctors -> axiom n <> mconcat [axiom n' | Ctor n' _ <- ctors]
