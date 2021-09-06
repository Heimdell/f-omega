
module Failure where

import Name
import Prog1
import Pretty

data Failure
  = Mismatch Prog Prog
  | Occurs Name Prog
  | ExpectedRecord Prog
  | ExpectedRecordToHaveField Name Prog
  | ExpectedForall Prog
  | UnexpectedAdditionaArgs [Pat]
  | ExpectedArgOfType Prog
  | NotFound Name
  | InternalError
  | While Operation Failure
  | Where [(Name, Prog)] Failure
  deriving (Show) via PP Failure

data Operation
  = InferringType Prog
  | InferringKind Prog
  | Deconstruct Prog (TDecl Prog)
  | Unifying Prog Prog

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

instance Pretty Failure where
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

    NotFound n ->
      "Name" |+| pp n |+| "is undefined or has escaped its scope"

    InternalError ->
      "Internal error"

    While op err ->
      pp err `above` "while" `indent` pp op

    Where ctx err ->
      pp err `above` "where" `indent` block [pp n |+| ":" |+| pp t | (n, t) <- ctx]
