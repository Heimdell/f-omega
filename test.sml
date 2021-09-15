let
  x = {a = 1, b = fun a -> a}
in
let
  show = ffi show : pi (a : Integer) -> String
in
x.b (show x.a)
