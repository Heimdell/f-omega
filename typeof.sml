
let
  typeof =
    --   +-- the type we are inferring
    --   |       +-- the value we use as source
    --   v       v
    fun (a : *) (b : a) -> a  -- we return type here

in
  --     +-- we put a hole here instead, for compiler to infer
  --     | +-- we put a known value
  --     v v
  typeof _ 1
