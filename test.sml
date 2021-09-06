
let
  data List (a : *) where
    | Nil  : List a
    | Cons : pi (x : a) -> pi (xs : List a) -> List a
in

let
  id = fun (a : *) (x : a) -> x
in
  id _ 1
