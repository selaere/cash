module Prim where

import Val (Val(..), CashMonad(..), Output(..), Error(..), Fun(..), L(..), ValErr(..))
import Arr (scalar, biscalar, catenate, construct, asAxes, reshape, agree, axesToVal, shape, spec, forceQuot)
import qualified Data.Text as T
import Data.Functor (($>))
import Data.Function (on)


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
  showErr = pure . Output . T.pack . show
  errAsVal _ = undefined

fromMaybeErr :: CashMonad m => Error e => e -> Maybe a -> m a
fromMaybeErr err = maybe (cashError err) pure


mathRat :: (L a, CashMonad m) => (Rational -> m Rational) -> a -> m Rational
mathRat f a = case toRat a of
  Just n  -> f n
  Nothing -> cashError (NotANumber (ltoelem a))
mathRat2 :: (L a, CashMonad m) => (Rational -> Rational -> m Rational) -> a -> a -> m Rational
mathRat2 f a b = case (toRat a, toRat b) of
  (Just a', Just b') -> f a' b'
  (Just _, Nothing) -> cashError (on NotANumber2 ltoelem b a)
  (_, _)            -> cashError (on NotANumber2 ltoelem a b)


monum :: CashMonad m => (Rational -> m Rational) -> Val -> m Val
monum f = scalar (spec (mathRat f))

binum :: CashMonad m => (Rational -> Rational -> m Rational) -> Val -> Val -> m Val
binum f = biscalar (cashError MismatchingAxes) (agree (mathRat2 f))

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

call :: CashMonad m => Val -> [Val] -> m [Val]
call = callQuot . forceQuot

exec :: CashMonad m => Fun -> [Val] -> m [Val]
exec FAdd = bi (ufbinum (+))
exec FSub = bi (ufbinum (-))
exec FMul = bi (ufbinum (*))
exec FDiv = bi (ufbinum (/))
exec FNot = mo (ufmonum (toRational . fromEnum . (== 0)))
exec FCat  = bi (fromMaybeErr ShapeError .: catenate)
exec FCons = bi (fromMaybeErr ShapeError .: construct)
exec FReshape = bi \x y -> fromMaybeErr ShapeError (reshape <$> asAxes y <*> pure x)
exec FShape   = mo (pure . axesToVal . shape)
exec FDrop = \case     (_:xs) -> pure        xs  ; xs -> udf 1 xs
exec FDup  = \case     (x:xs) -> pure   (x:x:xs) ; xs -> udf 1 xs
exec FSwap = \case   (y:x:xs) -> pure   (x:y:xs) ; xs -> udf 2 xs
exec FRot  = \case (z:y:x:xs) -> pure (x:z:y:xs) ; xs -> udf 3 xs
exec FOver = \case   (y:x:xs) -> pure (y:x:y:xs) ; xs -> udf 2 xs
exec FShow = mo0 (cashLog . Output . T.pack . show)
exec FCall = \case (x:xs) -> callQuot (forceQuot x) xs
                   xs     -> udf 1 xs
exec FBoth = \case (q:z:y:xs) -> do xs' <- call q (z:xs); call q (y:xs')
                   xs         -> udf 4 xs