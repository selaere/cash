module Prim where

import Val
import Arr
import qualified Data.Text as T
import qualified Control.Monad.Trans.State.Lazy as St
import Data.Functor (($>), (<&>))
import Data.Function (on)
import Data.Int (Int64)
import Control.Monad (guard, join, (>=>), foldM, when, unless, zipWithM)
import Data.Ratio (numerator, denominator)
import GHC.Real ((%))
import Control.Arrow ((>>>))
import qualified Data.Vector.Generic as V
import Data.Maybe (listToMaybe, fromMaybe)
import Control.Monad.Trans.Class (lift)

data PrimError
  = NotNumber
  | MismatchingAxes
  | Underflow Int Int
  | ShapeError
  | NotANumber Elem
  | NotANumber2 Elem Elem
  | NotANumberV Val
  | NotANumberV2 Val Val
  | CharOverflow
  | CharRational
  | NotAnInteger Val
  | NotACharacter Val
  | OutOfRange Val Val
  | NotAList Val
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
lazipMCash f a b = fromMaybeErr MismatchingAxes (lazip1 f a b)

-- detect binary function overflow in a generic way
overflow :: (forall a. Integral a => a->a->a) -> Int64 -> Int64 -> Maybe Int64
overflow op x y =
  let !z = op (toInteger x) (toInteger y) in
  guard (inBounds64 z) $> fromInteger z

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
and2 a b = tap (flip go) b a >>= fromMaybeErr NotNumber
  where
    go :: L b => Val -> Arr b -> m (Maybe Val)
    go (Elems a) b = Just <$> lazipCash goElem a (mapArr ltoelem b)
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

-- "or" function ( x y\ -> y if x null, otherwise y )
or2 :: forall m. CashMonad m => Val -> Val -> m Val
or2 = handleNum op op \cases
  (Chars a) (Chars b) -> lazipCash (pure .: \cases '\0' y -> y; x _ -> x) a b
  a         b         -> (lazipCash goElem `on` asElems) a b
  where
    op :: (Num x, Eq x) => x -> x -> x
    op 0 y = y
    op x _ = x

    goElem :: Elem -> Elem -> m Elem
    goElem (EBox x) (EBox y) = EBox <$> or2 x y
    goElem x (EBox y) = EBox <$> or2 (atoval (Atom x)) y
    goElem (ENum    0 ) y = pure y
    goElem (EChar '\0') y = pure y
    goElem (EBox    x ) y = EBox <$> or2 x (atoval (Atom y))
    goElem x _ = pure x

-- convenience. you can't define max and min in terms of this because of some type bullshit
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

doWithStack :: CashMonad m => ([Val] -> m [Val]) -> St.StateT [Val] m Val
doWithStack f = do
  (x',xs) <- pop =<< lift.f =<< St.get 
  St.put xs
  return x'

buildElems :: [Axis] -> [Elem] -> Val
buildElems sh z = case listToMaybe z of
  Just (ENum    _) -> build canInt     (build canENum elems)
  Just (EChar   _) -> build canEChar   elems
  Just (ESymbol _) -> build canESymbol elems
  Just (EPath   _) -> build canEPath   elems
  _                -> Elems (shapedl sh z)
  where
    elems = Elems (shapedl sh z)

    build :: L a => (Elem -> Maybe a) -> Val -> Val
    build can f = case traverse can z of
      Just z' -> atoval (shapedl sh z')
      Nothing -> f

map2 :: forall m. CashMonad m => Val -> Val -> [Val] -> m [Val]
map2 q a xs = tap results a <&> \(z, xs')-> buildElems (shape a) z : xs'
  where
    results :: L a => Arr a -> m ([Elem], [Val])
    results (Arr _ a) = St.runStateT (traverse step (V.toList a)) xs
    
    step :: L a => a -> St.StateT [Val] m Elem
    step x = asElem <$> doWithStack (call q . (atoval (Atom x) :))

zip2 :: forall m. CashMonad m => Val -> Val -> Val -> [Val] -> m [Val]
zip2 q a b xs = tap2 go a b <&> uncurry (:)
  where
    go :: (L a, L b) => Arr a -> Arr b -> m (Val, [Val])
    go a b = St.runStateT val xs
      where val = fromMaybe (cashError MismatchingAxes) (lazip1_ step a b) <&> uncurry buildElems
    
    step :: (L a, L b) => a -> b -> St.StateT [Val] m Elem
    step x y = asElem <$> doWithStack (call q . (atoval (Atom x) :) . (atoval (Atom y) :))

canInt     :: Elem -> Maybe Int64;    canInt     = \case (ENum x)->assertInt x; _ -> Nothing
canENum    :: Elem -> Maybe Rational; canENum    = \case (ENum x)    -> Just x; _ -> Nothing
canEChar   :: Elem -> Maybe Char;     canEChar   = \case (EChar x)   -> Just x; _ -> Nothing
canESymbol :: Elem -> Maybe Symbol;   canESymbol = \case (ESymbol x) -> Just x; _ -> Nothing
canEPath   :: Elem -> Maybe T.Text;   canEPath   = \case (EPath x)   -> Just x; _ -> Nothing

rankrel2 :: forall m. CashMonad m => Int -> Val -> Val -> [Val] -> m [Val]
rankrel2 n q a xs = tap go a
  where
    go :: L a => Arr a -> m [Val]
    go (Arr sh a) = St.runStateT val xs <&> uncurry (:)
      where
        (lsh,rsh) = splitAt n sh
        val = do
          z <- traverse (step . cellAt rsh a) (take (axesSize lsh) [0..])
          first <- case z of []  -> step (Atom 0 :: Arr Int64)
                             x:_ -> pure x
          buildVals lsh first z

    step :: L a => Arr a -> St.StateT [Val] m Val
    step x = doWithStack (call q . (atoval x :))

birankrel2 :: forall m. CashMonad m => Int -> Int -> Val -> Val -> Val -> [Val] -> m [Val]
birankrel2 r r' q a b xs = tap2 go a b
  where
    go :: (L a, L b) => Arr a -> Arr b -> m [Val]
    go (Arr sh a) (Arr sh' b) = St.runStateT val xs <&> uncurry (:)
      where
        (lsh ,rsh ) = splitAt r  sh
        (lsh',rsh') = splitAt r' sh'
        val = do
          (nlsh, i, i') <- fromMaybeErr MismatchingAxes (leadingAxis lsh lsh')
          z <- zipWithM (\j j'-> step (cellAt rsh a j) (cellAt rsh' b j')) i i'
          first <- case z of []  -> join step (Atom 0 :: Arr Int64)
                             x:_ -> pure x
          buildVals nlsh first z

    step :: (L a, L b) => Arr a -> Arr b -> St.StateT [Val] m Val
    step x y = doWithStack (call q . (atoval x :) . (atoval y :))

buildVals :: CashMonad m => [Axis] -> Val -> [Val] -> m Val
buildVals nlsh first z = 
  unless (all ((nrsh ==) . shape) z) (cashError MismatchingAxes) $>
  case first of
    Ints    _ -> build canInts (build canNums elems)
    Nums    _ -> build canNums elems
    Chars   _ -> build canChars elems
    Symbols _ -> build canSymbols elems
    Paths   _ -> build canPaths elems
    _         -> elems
  where
    nrsh = shape first
    nsh = nlsh <> nrsh
    elems = aggregate (asElems <$> z)

    aggregate :: L a => [Arr a] -> Val
    aggregate = atoval . Arr nsh . V.concat . fmap \(Arr _ a) -> a

    build :: L a => (Val -> Maybe (Arr a)) -> Val -> Val
    build can f = fromMaybe f (aggregate <$> traverse can z)

canInts    :: Val -> Maybe (Arr Int64);    canInts    = \case (Ints x)    -> Just x; _ -> Nothing
canNums    :: Val -> Maybe (Arr Rational); canNums    = \case (Nums x)    -> Just x; _ -> Nothing
canChars   :: Val -> Maybe (Arr Char);     canChars   = \case (Chars x)   -> Just x; _ -> Nothing
canSymbols :: Val -> Maybe (Arr Symbol);   canSymbols = \case (Symbols x) -> Just x; _ -> Nothing
canPaths   :: Val -> Maybe (Arr T.Text);   canPaths   = \case (Paths x)   -> Just x; _ -> Nothing

asInts :: Val -> Maybe (Arr Int64)
asInts (Ints n)  = Just n
asInts (Nums n)  = traverseArr assertInt n
asInts (Elems a) = traverseArr canInt a
asInts (Quot a)  = asInts (list a)
asInts _ = Nothing

asNums :: Val -> Maybe (Arr Rational)
asNums (Nums n)  = Just n
asNums (Ints n)  = Just (mapArr toRational n)
asNums (Elems a) = traverseArr canENum a
asNums (Quot a)  = asNums (list a)
asNums _ = Nothing

asChars :: Val -> Maybe (Arr Char)
asChars (Chars n) = Just n
asChars (Elems a) = traverseArr canEChar a
asChars (Quot a) = asChars (list a)
asChars _ = Nothing

select :: CashMonad m => Val -> Val -> m Val
select a bb@(Ints b) = fromMaybeErr (OutOfRange a bb) (tfmap (indexCells b) a)
select a bb@(Nums b) = fromMaybeErr (OutOfRange a bb) (tfmap (indexCells b) a)
select a bb = tap (\b -> fromMaybeErr (OutOfRange a bb) (tfmap (indexCellsByName b) a)) bb

pick :: forall m. CashMonad m => Val -> Val -> m Val
pick a bb = tap go bb
  where go :: L a => Arr a -> m Val
        go (Arr [] b) = go (Arr [Ixd 1] b)
        go (Arr [Ixd _] b) = fromMaybeErr (OutOfRange a bb) (unwrap <$> indexElement' b a)
        go _ = cashError (OutOfRange a bb)

boolInt :: Bool -> Int64
boolInt = toEnum . fromEnum

ufbinum :: CashMonad m => (Rational -> Rational -> Rational) -> Val -> Val -> m Val
ufbinum f = binum (pure .: f)

ufmonum :: CashMonad m => (Rational -> Rational) -> Val -> m Val
ufmonum f = monum (pure . f)

pop :: CashMonad m => [Val] -> m (Val,[Val])
pop (x:xs) = pure (x,xs)
pop []     = cashError (Underflow 1 0)

pop2 :: CashMonad m => [Val] -> m (Val,Val,[Val])
pop2 (x:y:xs) = pure (x,y,xs)
pop2 xs       = cashError (Underflow 2 (length xs))

pop3 :: CashMonad m => [Val] -> m (Val,Val,Val,[Val])
pop3 (x:y:z:xs) = pure (x,y,z,xs)
pop3 xs         = cashError (Underflow 3 (length xs))

pop4 :: CashMonad m => [Val] -> m (Val,Val,Val,Val,[Val])
pop4 (w:x:y:z:xs) = pure (w,x,y,z,xs)
pop4 xs           = cashError (Underflow 4 (length xs))

pop5 :: CashMonad m => [Val] -> m (Val,Val,Val,Val,Val,[Val])
pop5 (v:w:x:y:z:xs) = pure (v,w,x,y,z,xs)
pop5 xs             = cashError (Underflow 5 (length xs))

-- binary function, 1 output
bi :: CashMonad m => (Val -> Val -> m Val) -> [Val] -> m [Val]
bi f = pop2 >=> \(y,x,xs)-> (:xs) <$> f x y

-- unary function, 1 output
mo :: CashMonad m => (Val -> m Val) -> [Val] -> m [Val]
mo f = pop >=> \(x,xs)-> (:xs) <$> f x

-- unary function, 0 outputs
mo0 :: CashMonad m => (Val -> m ()) -> [Val] -> m [Val]
mo0 f = pop >=> \(x,xs)-> f x $> xs

-- call a quotation as a value
call :: CashMonad m => Val -> [Val] -> m [Val]
call = callQuot . forceQuot

quotS :: Int64 -> Int64 -> Maybe Int64
quotS x y | x == maxBound && y /= -1 = Nothing
          | otherwise                = Just (x `quot` y)

powr :: Rational -> Rational -> Rational
powr x y | denominator y == 1 = x^numerator y
         | otherwise          = toRational (on (**) fromRational x y :: Double)

exec :: CashMonad m => Fun -> [Val] -> m [Val]
exec FAdd  = bi add
exec FSub  = bi sub
exec FMul  = bi (overflowingOp (*) (overflow (*)))
exec FDiv  = bi (binum (pure.:(/)))
exec FLt   = bi (compOp (boolInt.:(<)) )
exec FEq   = bi (compOp (boolInt.:(==)))
exec FGt   = bi (compOp (boolInt.:(>)) )
exec FDivi = bi (overflowingOp (\x y->toRational (floor (x/y) :: Integer)) quotS)
exec FMod  = bi (overflowingOp (\x y-> x-y*(floor (x/y) % 1)) (Just .: rem))
exec FPow  = bi (overflowingOp powr (overflow (^)))
exec FMax  = bi (agreeOp max max max)
exec FMin  = bi (agreeOp min min min)
exec FAnd  = bi and2
exec FOr   = bi or2
exec FNot  = mo (monum (pure . toRational . fromEnum . (== 0)))
exec FCat  = bi (fromMaybeErr ShapeError .: catenate)
exec FCons = bi (fromMaybeErr ShapeError .: construct)
exec FReshape = bi \x y -> fromMaybeErr ShapeError (reshape <$> asAxes y <*> pure x)
exec FShape= mo (pure . axesToVal . shape)
exec FDrop = pop  >>> fmap \    (_,xs)->       xs  {- HLINT ignore -}
exec FDup  = pop  >>> fmap \    (x,xs)->   x:x:xs
exec FSwap = pop2 >>> fmap \  (y,x,xs)->   x:y:xs
exec FRot  = pop3 >>> fmap \(z,y,x,xs)-> x:z:y:xs
exec FOver = pop2 >>> fmap \  (y,x,xs)-> y:x:y:xs
exec FShow = mo0 (cashLog . Output . T.pack . show)
exec FCall = pop >=> uncurry call
exec FBoth = pop3 >=> \(q,z,y,xs) -> do xs' <- call q (y:xs); call q (z:xs')
exec FIf   = pop3 >=> \(q,p,c,xs) -> do c <- assertBoolVal c; call (if c then p else q) xs
exec FDip  = pop2 >=> \(q,z,xs)-> do xs' <- call q    xs ; return (z:xs')
exec FKeep = pop2 >=> \(q,z,xs)-> do xs' <- call q (z:xs); return (z:xs')
exec FWhile= pop2 >=> \(q,p,xs)->while q p xs
exec FTimes= pop2 >=> \(q,n,xs)->
  do n <- fromMaybeErr (NotANumberV n) (unwrapAtom n >>= toRat)
     when (denominator n /= 1) (cashError (NotAnInteger (Nums (Atom n))))
     foldM (\xs' ()-> call q xs') xs (replicate (fromEnum (numerator n)) ())
exec FMap   = pop2 >=> \(q,x,xs)->map2 q x xs
exec FZip   = pop3 >=> \(q,x,y,xs)->zip2 q x y xs
exec FCells = pop2 >=> \(q,x,xs)->rankrel2 1 q x xs
exec FRank  = pop3 >=> \(q,r,x,xs)->rankNumberC x r >>= \r -> rankrel2 r q x xs
exec FBicells = pop3 >=> \(q,a,b,xs)-> birankrel2 1 1 q a b xs
exec FBirank  = pop5 >=> \(q,r,r',a,b,xs)-> do r  <- rankNumberC a r
                                               r' <- rankNumberC b r'
                                               birankrel2 r r' q a b xs
exec FAsInts  = mo \x-> fromMaybeErr (NotANumberV   x) (Ints <$> asInts  x)
exec FAsNums  = mo \x-> fromMaybeErr (NotAnInteger  x) (Nums <$> asNums  x)
exec FAsChars = mo \x-> fromMaybeErr (NotACharacter x) (Chars<$> asChars x)
exec FAsElems = mo (pure . Elems . asElems)
exec FPick    = bi pick
exec FSelect  = bi select

rankNumberC :: CashMonad m => Val -> Val -> m Int
rankNumberC (shape -> length -> len) r =
  fromMaybeErr (NotANumberV r) (fmap fromEnum . assertInt =<< singleRat r)
  <&> \r -> if r < 0 then min len (-r)
                     else max 0 (len - r)

while :: CashMonad m => Val -> Val -> [Val] -> m [Val]
while q p xs = do
    (c,xs') <- pop =<< call p xs
    c <- assertBoolVal c
    if c then while q p =<< call q xs'
         else return xs'

assertBoolVal :: CashMonad m => Val -> m Bool
assertBoolVal x = fromMaybeErr (NotANumberV x) (valIsTrue x)
