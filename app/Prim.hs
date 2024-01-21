module Prim where

import Val (Val(..), CashMonad(..), Output(..), Error(..), Elem (..), Fun(..))
import Arr (scalar, biscalar, catenate, construct, asAxes, reshape)
import qualified Data.Text as T
import Control.Monad ((>=>))
import Data.Functor (($>))


infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

data PrimError
  = NotNumber
  | MismatchingAxes
  | Underflow Int Int
  | ShapeError
  deriving (Eq, Show)

instance Error PrimError where
  --showErr NotNumber       = Output (T.pack "not a number")
  --showErr MismatchingAxes = Output (T.pack "mismatching axes")
  --showErr (Underflow a b) = Output (T.pack
  --  ("stack underflow: need at least "<>show a<>" values on stack, i have "<>show b))
  showErr x = Output (T.pack (show x))
  errAsVal _ = undefined

fromMaybeErr :: CashMonad m => Error e => e -> Maybe a -> m a
fromMaybeErr err = maybe (cashError err) pure

number :: Elem -> Maybe Rational
number (ENum x)  = Just x
number (EChar c) = Just (toRational (fromEnum c))
number _         = Nothing

numberCash :: CashMonad m => Elem -> m Rational
numberCash = fromMaybeErr NotNumber . number

monum :: CashMonad m => (Rational -> m Rational) -> Val -> m Val
monum f = scalar (numberCash >=> fmap ENum . f)

binum :: CashMonad m => (Rational -> Rational -> m Rational) -> Val -> Val -> m Val
binum f =
  biscalar (cashError MismatchingAxes) \a b -> do
    a' <- numberCash a
    b' <- numberCash b
    ENum <$> f a' b'

ufbinum :: CashMonad m => (Rational -> Rational -> Rational) -> Val -> Val -> m Val
ufbinum f = binum (pure .: f)

ufmonum :: CashMonad m => (Rational -> Rational) -> Val -> m Val
ufmonum f = monum (pure . f)

udf :: CashMonad m => Int -> [a] -> m b
udf n = cashError . Underflow n . length

bi :: CashMonad m => (Val -> Val -> m Val) -> [Val] -> m [Val]
bi f (y:x:xs) = (:xs) <$> f x y
bi _ xs       = udf 2 xs


mo :: CashMonad m => (Val -> m Val) -> [Val] -> m [Val]
mo f (x:xs) = (:xs) <$> f x
mo _ xs     = udf 1 xs


mo0 :: CashMonad m => (Val -> m ()) -> [Val] -> m [Val]
mo0 f (x:xs) = f x $> xs
mo0 _ xs     = udf 1 xs

exec :: CashMonad m => Fun -> [Val] -> m [Val]
exec FAdd = bi (ufbinum (+))
exec FSub = bi (ufbinum (-))
exec FMul = bi (ufbinum (*))
exec FDiv = bi (ufbinum (/))
exec FNeg = mo (ufmonum negate)
exec FCat = bi (fromMaybeErr ShapeError .: catenate)
exec FCons = bi (fromMaybeErr ShapeError .: construct)
exec FReshape = bi \x y -> fromMaybeErr ShapeError (reshape <$> asAxes x <*> pure y)
exec FDrop = \case     (_:xs) -> pure        xs  ; xs -> udf 1 xs
exec FDup  = \case     (x:xs) -> pure   (x:x:xs) ; xs -> udf 1 xs
exec FSwap = \case   (y:x:xs) -> pure   (x:y:xs) ; xs -> udf 2 xs
exec FRot  = \case (z:y:x:xs) -> pure (y:x:z:xs) ; xs -> udf 3 xs
exec FOver = \case   (y:x:xs) -> pure (y:x:y:xs) ; xs -> udf 2 xs
exec FShow = mo0 (cashLog . Output . T.pack . show)