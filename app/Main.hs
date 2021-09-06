
import System.Environment

import Polysemy
import Polysemy.Error

import Parser1
import Eval1
import Infer1
import Unify1
import Context1

main :: IO ()
main = do
  [fin] <- getArgs
  parseFile parseProg fin >>= \case
    Right prog -> do
      e <- runM $ runContext $ evalUnification $ do
        (prog', ty) <- inference prog
        embed do
          putStrLn "---- Inferred ----"
          print prog'
          putStrLn ""
          putStrLn "---- Type ----"
          print ty
          putStrLn ""
          putStrLn "---- Evals ----"
          print (eval prog')
          return ()

      print e

    Left err -> do
      print err
