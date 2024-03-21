module Prim where

import Val (Val(..), CashMonad(..), Output(..), Error(..), Fun(..), L(..), Elem(..), Arr)
import Arr (agree, asAxes, asElems, axesToVal, biscalar, catenate, construct, fmapArr, forceQuot
          , lazip1, reshape, scalar, shape, spec, pattern Atom)
      --  ^ randome comma
import qualified Data.Text as T
import Data.Functor (($>))
import Data.Function (on)
import Data.Int (Int64)
import Control.Monad (guard, when, join)


infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

data PrimError
  = NotNumber
  | MismatchingAxes
  | Underflow Int Int
  | ShapeError
  | NotANumber Elem
  | NotANumber2 Elem Elem
  | CharOverflow
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

lazipCash :: (CashMonad m, L a, L b, L c) => (a -> b -> m c) -> Arr a -> Arr b -> m (Arr c)
lazipCash f = join .: lazipMCash f

lazipMCash :: (CashMonad m, Applicative n, L a, L b, L c) =>
              (a -> b -> n c) -> Arr a -> Arr b -> m (n (Arr c))
lazipMCash f a b = maybe (cashError MismatchingAxes) pure (lazip1 f a b)

overflowingOp :: forall m. CashMonad m =>
                 (forall a. Num a => a->a->a) -> Val -> Val -> m Val
overflowingOp op = go
  where
    go :: Val -> Val -> m Val
    go (Ints a) (Ints b) =
      lazipMCash go64 a b >>= \case
        Just c  -> pure (Ints c)
        Nothing -> Nums <$> lazipCash (pure .: op `on` toRational) a b
    go (Nums a) (Nums b) = Nums <$> lazipCash (pure.:op) a b
    go (Chars a) (Ints  b) = Chars <$> lazipCash goChr a b
    go (Ints  a) (Chars b) = Chars <$> lazipCash goChr a b
    go (Ints a)      b  = go   (Nums (fmapArr toRational a)) b
    go       a (Ints b) = go a (Nums (fmapArr toRational b))
    go a b = Elems <$> (lazipCash goElem `on` asElems) a b

    go64 :: Int64 -> Int64 -> Maybe Int64
    go64 x y = --nitnendo
      let !z = op (toInteger x) (toInteger y) in
      guard (toInteger (minBound::Int64) <= z && z <= toInteger (maxBound::Int64))
      $> fromInteger z

    goChr :: (Enum a, Enum b) => a -> b -> m Char
    goChr x y =
      let !z = op (toInteger (fromEnum x)) (toInteger (fromEnum y)) in
      when (0 <= z && z <= 0x10FFFF) (cashError CharOverflow)
      $> toEnum (fromInteger z)

    goElem :: Elem -> Elem -> m Elem
    goElem (ENum a) (ENum b) = pure (ENum (op a b))
    goElem (EBox a) (ENum b) = EBox <$> overflowingOp op a (Nums (Atom b))
    goElem (ENum a) (EBox b) = EBox <$> overflowingOp op (Nums (Atom a)) b
    goElem (EBox a) (EBox b) = EBox <$> overflowingOp op a b
    goElem a b = cashError (NotANumber2 a b)

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
exec FAdd = bi (overflowingOp (+))
exec FSub = bi (overflowingOp (-))
exec FMul = bi (overflowingOp (*))
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