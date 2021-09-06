
{- | Helpers for producing pretty prints.
-}

module Color where

type Color = (Int, Int)

toCode :: Color -> String
toCode (hue, -1) = show (30 + hue) ++ ";2"
toCode (hue,  0) = show (90 + hue)
toCode (hue,  1) = show (30 + hue) ++ ";1"
toCode  c        = error $ "toCode: should be (0..16 (15?), -1.. 1), but it is " ++ show c

faint :: Color -> Color
faint (h, _) = (h, -1)

bright :: Color -> Color
bright (h, _) = (h, 1)

red :: Color
red = (1, 0)

green :: Color
green = (2, 0)

blue :: Color
blue = (4, 0)

black :: Color
black = (0, 0)

(+!) :: Color -> Color -> Color
(a, _) +! (b, _) = (a + b, 0)

yellow :: Color
yellow = green +! red

cyan :: Color
cyan = green +! blue

magenta :: Color
magenta = red +! blue

white :: Color
white = red +! blue +! green
