
{- | An extension of 'Text.PrettyPrint'.
-}

module Pretty
  ( module Pretty
  , module Text.PrettyPrint
  , module Color
  )
  where

import Control.Monad (liftM2, liftM3)

import qualified Data.Text as Text
import Data.Text (Text, pack)
import Data.String (IsString (..))

import Polysemy
import Polysemy.Reader

import Text.PrettyPrint hiding ((<>))

import Color

-- | Pretty-print to `Text`. Through `String`. Yep.
ppToText :: Pretty a => a -> Text
ppToText = pack . show . pretty

type Printer = Sem '[Reader Int] Doc

instance Show Printer where
  show = show . retract

{- | A typeclass for pretty-printable stuff.
-}
class Pretty p where
  pp :: p -> Printer

pp' :: Pretty p => p -> Printer
pp' = closed . pp

pretty :: Pretty p => p -> Doc
pretty = retract . pp

retract :: Printer -> Doc
retract = run . runReader 10

(|+|), (|.|) :: Printer -> Printer -> Printer
(|+|) = liftM2 (<+>)
(|.|) = liftM2 (<.>)

instance IsString Printer where
  fromString = return . fromString

makePar :: (Printer, Printer) -> Int -> Printer -> Printer
makePar (open, close) prec1 act = do
  res   <- prec prec1 act
  prec0 <- ask
  return
    if prec0 <= prec1
    then retract open <> res <> retract close
    else res

prec :: Int -> Printer -> Printer
prec = local . const

closed :: Printer -> Printer
closed = prec 10

instance Pretty () where
  pp _ = "()"

instance Pretty1 Maybe where
  pp1 = maybe (return empty) pp

instance {-# OVERLAPS #-} (Pretty a, Pretty b) => Pretty (Either a b) where
  pp = either pp pp

instance Pretty Int where
  pp = return . int

instance Pretty Integer where
  pp = return . integer

instance Pretty Float where
  pp = return . float

instance Pretty Double where
  pp = return . double

-- | Common instance.
instance Pretty Text where
  pp = return . text . Text.unpack

-- | Common instance.
instance Pretty Doc where
  pp = return

-- | Common instance.
instance Pretty Printer where
  pp = id

{- | A typeclass for pretty-printable functors.
-}
class Pretty1 p where
  pp1 :: p Doc -> Printer

instance {-# OVERLAPPABLE #-} (Pretty a, Pretty1 p, Traversable p) => Pretty (p a) where
  pp ps = traverse pp ps >>= pp1

instance Pretty1 [] where
  pp1 = list

{- | A wrapper to make `Show` instances from `Pretty` ones.

     > data X a = X
     >   deriving Show via PP (X a)
-}
newtype PP a = PP { unPP :: a }

instance Pretty a => Show (PP a) where
  show = show . pretty . unPP

{- | The class for annotations.
-}
class Modifies d where
  ascribe :: d -> Printer -> Printer

instance Modifies () where
  ascribe () = id

{- | The replacement for `Text.PrettyPrint.<>`.
-}
infixl 6 <.>
(<.>) :: Doc -> Doc -> Doc
(<.>) = (<>)

-- | Colorize a `Doc`.
color :: Color -> Printer -> Printer
color c d = do
  r <- d
  return $ zeroWidthText begin <.> r <.> zeroWidthText end
  where
    begin = "\x1b[" ++ toCode c ++ "m"
    end   = "\x1b[0m"

seq' :: Pretty p => [p] -> Printer
seq' ps = fsep <$> traverse pp ps

-- | Decorate list of stuff as a tuple.
tuple :: Pretty p => [p] -> Printer
tuple ps = parens <$> closed (train "," =<< traverse pp ps)

-- | Decorate list of stuff as a tuple.
record :: Pretty p => [p] -> Printer
record ps = braces <$> closed (train "," =<< traverse pp ps)

-- | Decorate list of stuff as a list.
list :: Pretty p => [p] -> Printer
list ps = brackets <$> closed (train ";" ps)

infixr 2 `indent`
-- | First argument is a header to an indented second one.
indent :: Printer -> Printer -> Printer
indent a b = liftM3 hang (closed a) (pure 2) (closed b)

infixr 1 `above`
-- | Horisontal composition.
above :: Printer -> Printer -> Printer
above a b = liftM3 hang (closed a) (pure 0) (closed b)

-- | Pretty print as a sequence with given separator.
train :: Pretty p => Printer -> [p] -> Printer
train sep' ps = punctuate' sep' (map pp ps)

punctuate' :: Printer -> [Printer] -> Printer
punctuate' _ [p] = p
punctuate' _ [] = return empty
punctuate' sep' (p : ps) = p |.| sep' |+| punctuate' sep' ps

-- | Pretty print as a vertical block.
block :: Pretty p => [p] -> Printer
block = closed . foldr (liftM2 ($+$)) (pure empty) . map pp

-- | For pretty-printing qualified names.
sepByDot :: Pretty p => [p] -> Printer
sepByDot (p : ps) = foldr (\a b -> a |.| "." |.| b) (pp p) (map pp ps)
sepByDot []       = pure empty

-- | For pretty-printing `Maybe`s.
mb :: Pretty a => (Printer -> Printer) -> Maybe a -> Printer
mb f = maybe (pure empty) (f . pp)

-- | Pretty print as a vertical with elements separated by newline.
sparseBlock :: Pretty a => [a] -> Printer
sparseBlock = closed . pure . vcat . punctuate "\n" . map (($$ empty) . pretty)
