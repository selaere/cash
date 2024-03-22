module Prim where

import Val (Val(..), CashMonad(..), Output(..), Error(..), Fun(..), L(..), Elem(..), Arr)
import Arr (agree, asAxes, asElems, axesToVal, biscalar, catenate, construct, forceQuot
          , lazip1, reshape, scalar, shape, spec, pattern Atom, tap, fmapArr)
      --  ^ randome comma
import qualified Data.Text as T
import Data.Functor (($>), (<&>))
import Data.Function (on)
import Data.Int (Int64)
import Control.Monad (guard, join)
import Data.Ratio (numerator, denominator)
import GHC.Real ((%))


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
  | CharRational
  deriving (Eq, Show)

instance Error PrimError where
  showErr = pure . Output . T.pack . show
  errAsVal _ = undefined

fromMaybeErr :: CashMonad m => Error e => e -> Maybe a -> m a
fromMaybeErr err = maybe (cashError err) pure


mathRat :: (L a, CashMonad m) => (Rational -> m Rational) -> a -> m Rational
mathRat f x = case toRat x of
  Just x  -> f x
  Nothing -> cashError (NotANumber (ltoelem x))
mathRat2 :: (L a, CashMonad m) => (Rational -> Rational -> m Rational) -> a -> a -> m Rational
mathRat2 f x y = case (toRat x, toRat y) of
  (Just x, Just y ) -> f x y
  (Just _, Nothing) -> cashError (on NotANumber2 ltoelem y x)
  (_, _)            -> cashError (on NotANumber2 ltoelem x y)

monum :: CashMonad m => (Rational -> m Rational) -> Val -> m Val
monum f = scalar (spec (mathRat f))

binum :: CashMonad m => (Rational -> Rational -> m Rational) -> Val -> Val -> m Val
binum f = biscalar (cashError MismatchingAxes) (agree (mathRat2 f))

-- leading-axis agreement to a value in a Cash monad
lazipCash :: (CashMonad m, L a, L b, L c) => (a -> b -> m c) -> Arr a -> Arr b -> m Val
lazipCash f = fmap atoval . join .: lazipMCash f

lazipMCash :: (CashMonad m, Applicative n, L a, L b, L c) =>
              (a -> b -> n c) -> Arr a -> Arr b -> m (n (Arr c))
lazipMCash f a b = maybe (cashError MismatchingAxes) pure (lazip1 f a b)

-- detect binary function overflow in a generic way
overflow :: (forall a. Integral a => a->a->a) -> Int64 -> Int64 -> Maybe Int64
overflow op x y =
  let !z = op (toInteger x) (toInteger y) in
  guard (toInteger (minBound::Int64) <= z && z <= toInteger (maxBound::Int64))
  $> fromInteger z

-- used with character arithmetic
assertInteger :: CashMonad m => Rational -> m Integer
assertInteger x = if denominator x == 1 then pure (numerator x) else cashError CharRational

-- handles binary operations with number elements. otherwise, raise an error
handleElemNum :: (CashMonad m, L a) =>
                 (Val->Val->m Val) -> (Rational->Rational->a) ->
                 Elem -> Elem -> m Elem
handleElemNum recur op = \cases
  (ENum x) (ENum y) -> pure (ltoelem (op x y))
  (EBox x) (EBox y) -> EBox <$> recur x y
  (EBox x) y        -> EBox <$> recur x (atoval (Atom y))
  x        (EBox y) -> EBox <$> recur   (atoval (Atom x)) y
  x        y        -> cashError (NotANumber2 x y)

-- handles binary operations with typed number arrays.
-- then, passes along arguments to `alt`. use this to handle extra cases, like
--   character arithmetic or pervasion
handleNum :: (CashMonad m, L a, L b) =>
             (Rational->Rational->a) -> (Int64->Int64->b) -> (Val->Val->m Val) ->
             Val -> Val -> m Val
handleNum op op64 alt = go
  where
    go (Ints  a) (Ints  b) = lazipCash (pure.:op64) a b
    go (Nums  a) (Nums  b) = lazipCash (pure.:op) a b
    go (Ints  a) (Nums  b) = lazipCash (pure.: \x y-> op (toRational x) y) a b
    go (Nums  a) (Ints  b) = lazipCash (pure.: \x y-> op x (toRational y)) a b
    go a b = alt a b

-- handles binary operations with typed number arrays. but this time they can OVERFLOW
handleNumOverf :: (CashMonad m, L a, L b) =>
                  (Rational->Rational->a) -> (Int64->Int64->Maybe b) -> (Val->Val->m Val) ->
                  Val -> Val -> m Val
handleNumOverf op op64 alt = go
  where
    go (Ints  a) (Ints  b) =
      lazipMCash op64 a b >>= \case
        Just c  -> pure (atoval c)
        Nothing -> lazipCash (pure .: op `on` toRational) a b
    go a b = handleNum op (\_ _->undefined::Int64) alt a b


advChr :: forall m n. CashMonad m => (Num n, Ord n, Enum n) => Char -> n -> m Char
advChr x y | 0 <= z && z <= 0x10FFFF = pure (toEnum (fromEnum z))
           | otherwise               = cashError CharOverflow
  where z = toEnum (fromEnum x) + y :: n

retrChr :: forall m n. CashMonad m => (Num n, Ord n, Enum n) => Char -> n -> m Char
retrChr x y = advChr x (-y)

-- addition function that handles affine transformations to characters (n+c, c+n)
add :: forall m. CashMonad m => Val -> Val -> m Val
add = handleNumOverf (+) (overflow (+)) \cases
  (Chars a) (Ints  b) -> lazipCash advChr a b
  (Ints  a) (Chars b) -> lazipCash advChr b a
  (Chars a) (Nums  b) -> lazipCash (\x y-> advChr x =<< assertInteger y) a b
  (Nums  a) (Chars b) -> lazipCash (\x y-> advChr x =<< assertInteger y) b a
  a         b         -> (lazipCash goElem `on` asElems) a b
  where
    goElem :: Elem -> Elem -> m Elem
    goElem (EChar x) (ENum  y) = EChar <$> (advChr x =<< assertInteger y)
    goElem (ENum  x) (EChar y) = EChar <$> (advChr y =<< assertInteger x)
    goElem x y = handleElemNum add (+) x y

-- subtraction function that handles affine transformations to characters (c-n, c-c)
sub :: forall m. CashMonad m => Val -> Val -> m Val
sub = handleNumOverf (-) (overflow (-)) \cases
  (Chars a) (Ints  b) -> lazipCash retrChr a b
  (Chars a) (Nums  b) -> lazipCash (\x y-> retrChr x =<< assertInteger y) a b
  (Chars a) (Chars b) -> lazipCash (pure. toEnum @Int64 .: on (-) fromEnum) a b
  a         b         -> (lazipCash goElem `on` asElems) a b
  where
    goElem :: Elem -> Elem -> m Elem
    goElem (EChar x) (ENum  y) = EChar <$> (retrChr x =<< assertInteger y)
    goElem (ENum  x) (EChar y) = EChar <$> (retrChr y =<< assertInteger x)
    goElem (EChar x) (EChar y) = pure (ENum (toRational (on (-) fromEnum x y)))
    goElem x y = handleElemNum sub (-) x y

-- "and" function. implemented specially because we dont need to match up the types.
-- (the result of `x y&` is always the same type as x)
and2 :: forall m. CashMonad m => Val -> Val -> m Val
and2 a b = tap (flip go) b a >>= maybe (cashError NotNumber) pure
  where
    go :: L b => Val -> Arr b -> m (Maybe Val)
    go (Elems a) b = Just <$> lazipCash goElem a (fmapArr ltoelem b)
    go (Nums  a) b = fmap atoval <$> lazipMCash op a b
    go (Ints  a) b = fmap atoval <$> lazipMCash op a b
    go (Chars a) b = fmap atoval <$> lazipMCash op a b
    go _ _ = pure Nothing

    op :: (Enum x, L y) => x -> y -> Maybe x
    op x y = toRat y <&> \cases { 0 -> toEnum 0; _ -> x }

    goElem :: Elem -> Elem -> m Elem
    goElem (EChar _) (ENum  0) = pure (EChar '\0')
    goElem (EChar x) (ENum  _) = pure (EChar x)
    goElem (EChar _) (EChar '\0') = pure (EChar '\0')
    goElem (EChar x) (EChar _   ) = pure (EChar x)
    goElem x y = handleElemNum and2 (\cases _ 0->0; x _->x) x y

-- "or" function
or2 :: forall m. CashMonad m => Val -> Val -> m Val
or2 = handleNum op op \cases
  (Chars a) (Chars b) -> lazipCash (pure .: \cases '\0' y -> y; x _ -> x) a b
  a         b         -> (lazipCash goElem `on` asElems) a b
  where
    op :: (Num x, Eq x) => x -> x -> x
    op = \cases   0  y -> y; x _ -> x

    goElem :: Elem -> Elem -> m Elem
    goElem (EBox x) (EBox y) = EBox <$> or2 x y
    goElem x (EBox y) = EBox <$> or2 (atoval (Atom x)) y
    goElem (ENum    0 ) y = pure y
    goElem (EChar '\0') y = pure y
    goElem (EBox x) y = EBox <$> or2 x (atoval (Atom y))
    goElem x _ = pure x
    
-- convenience. you cant define max and min in terms of this because of some type bullshit
compOp :: forall m. CashMonad m =>
          (forall n. (Enum n, Ord n) => n->n->Int64) ->
          Val -> Val -> m Val
compOp op = agreeOp op op op

-- make a binary function that matches up argument types and calls a different function for
-- rationals, integers or characters. used for max, min, and comparisons
agreeOp :: forall m a b c. (CashMonad m, L a, L b, L c) =>
          (Rational->Rational->a) -> (Int64->Int64->b) -> (Char->Char->c) ->
          Val -> Val -> m Val
agreeOp op op64 opChr =  go
  where
    go :: Val -> Val -> m Val
    go = handleNum op op64 \cases
      (Chars a) (Chars b) -> lazipCash (pure.:opChr) a b
      a         b         -> (lazipCash goElem `on` asElems) a b

    goElem :: Elem -> Elem -> m Elem
    goElem (EChar x) (EChar y) = pure (ltoelem (opChr x y))
    goElem x         y         = handleElemNum go op x y

-- make a binary function that may overflow integers to rationals. doesn't handle characters
overflowingOp :: forall m a b. (CashMonad m, L a, L b) =>
                 (Rational->Rational->a) -> (Int64->Int64->Maybe b)
                 -> Val -> Val -> m Val
overflowingOp op op64 = go
  where go = handleNumOverf op op64 (lazipCash goElem `on` asElems)
        goElem = handleElemNum go op

staticOp :: forall m. CashMonad m =>
            (forall n. Real n => n->n->n)
            -> Val -> Val -> m Val
staticOp op = overflowingOp op (pure .: op)

bool :: Bool -> Int64
bool = toEnum . fromEnum

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

quotS :: Int64 -> Int64 -> Maybe Int64
quotS x y | x == maxBound && y /= -1 = Nothing
          | otherwise                = Just (x `quot` y)

powr :: Rational -> Rational -> Rational
powr x y | denominator y == 1 = x^numerator y
         | otherwise          = toRational (on (**) fromRational x y :: Double)

exec :: CashMonad m => Fun -> [Val] -> m [Val]
exec FAdd = bi add
exec FSub = bi sub
exec FMul = bi (overflowingOp (*) (overflow (*)))
exec FDiv = bi (ufbinum (/))
exec FLt  = bi (compOp (bool.:(<)) )
exec FEq  = bi (compOp (bool.:(==)))
exec FGt  = bi (compOp (bool.:(>)) )
exec FDivi= bi (overflowingOp (\x y->toRational (floor (x/y) :: Integer)) quotS)
exec FMod = bi (overflowingOp (\x y-> x-y*(floor (x/y) % 1)) (Just .: rem))
exec FPow = bi (overflowingOp powr (overflow (^)))
exec FMax = bi (agreeOp max max max)
exec FMin = bi (agreeOp min min min)
exec FAnd = bi and2
exec FOr  = bi or2
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
exec FBoth = \case (q:z:y:xs) -> do xs' <- call q (y:xs); call q (z:xs')
                   xs         -> udf 4 xs