module Arr where

import qualified Data.Vector.Generic as V
import qualified Data.Vector as VB
import qualified Data.Vector.Generic.Mutable as VM
import qualified Data.HashMap.Strict as HM
import Control.Exception (assert)
import Data.Function (on)
import Control.Monad (guard, zipWithM)
import Data.Functor (($>), (<&>))
import Val (pattern Names, Val(..), Axis(..), Elem(..), Bivector(..), Arr(..), L(..), Vec)
import Data.Maybe (fromMaybe)
import Data.Coerce (coerce)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))


infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)


pattern Atom :: L a => a -> Arr a
pattern Atom a <- Arr [] (V.head -> a) where Atom a = Arr [] (V.singleton a)

list :: [Elem] -> Val
list = atoval . listl

listl :: L a => [a] -> Arr a
listl = vecl . V.fromList

vec :: L a => Vec a -> Val
vec = atoval . vecl

vecl :: L a => Vec a -> Arr a
vecl elems = Arr [Ixd (V.length elems)] elems

shapel :: Arr a -> [Axis]
shapel (Arr sh _) = sh

shape :: Val -> [Axis]
shape = tap shapel

axisLength :: Axis -> Int
axisLength (Ixd l) = l
axisLength (Names ie) = length ie

axesSize :: [Axis] -> Int
axesSize = product . map axisLength

singleton :: Elem -> Val
singleton = atoval . singletonl

singletonl :: L a => a -> Arr a
singletonl a = Arr [Ixd 1] (V.fromList [a])

pair :: Elem -> Elem -> Val
pair = atoval .: pairl

pairl :: L a => a -> a -> Arr a
pairl a b = Arr [Ixd 2] (V.fromList [a,b])

vchunksOf :: V.Vector v a => Int -> v a -> [v a]
vchunksOf i v = go v
  where go v =
          let (l,r) = V.splitAt i v in
          if V.null l then [] else l : go r

tfmapb :: L b => Functor f => (forall a. L a => Arr a -> f (Arr b)) -> Val -> f Val
tfmapb f = tap (fmap atoval . f)

tmapb :: L b => (forall a. L a => Arr a -> Arr b) -> Val -> Val
tmapb f = coerce (tfmapb (Identity . f))

tfmap :: Functor f => (forall a. L a => Arr a -> f (Arr a)) -> Val -> f Val
tfmap f = tap (fmap atoval . f)

tmap :: (forall a. L a => Arr a -> Arr a) -> Val -> Val
tmap f = coerce (tfmap (Identity . f))

tmapq :: (forall a. L a => Arr a -> Arr a) -> ([Elem] -> [Elem]) -> Val -> Val
tmapq f = coerce (tfmapq (Identity . f))

tmapor :: (forall a. L a => Arr a -> Arr a) -> ([Elem] -> Val) -> Val -> Val
tmapor f = coerce (tfmapor (Identity . f))

tfmapq :: Functor f => (forall a. L a => Arr a -> f (Arr a)) -> ([Elem] -> f [Elem]) -> Val -> f Val
tfmapq f g = tfmapor f (fmap Quot . g)

tfmapor :: Functor f => (forall a. L a => Arr a -> f (Arr a)) -> ([Elem] -> f Val) -> Val -> f Val
tfmapor f = tapq (fmap atoval . f)

tap :: (forall a. L a => Arr a -> b) -> Val -> b
tap f = tapq f (f . listl)

tapq :: (forall a. L a => Arr a -> b) -> ([Elem] -> b) -> Val -> b
tapq f _ (Ints    x) = f x
tapq f _ (Nums    x) = f x
tapq f _ (Chars   x) = f x
tapq f _ (Symbols x) = f x
tapq f _ (Paths   x) = f x
tapq f _ (Elems   x) = f x
tapq _ g (Quot    x) = g x

traverseA :: (Applicative f, L a, L b) => (a -> f b) -> Arr a -> f (Arr b)
traverseA f (Arr sh a) = Arr sh . V.fromList <$> traverse f (V.toList a)

traverseA' :: (Applicative f, L a, L b, Vec a ~ Vec b) => (a -> f b) -> Arr a -> f (Arr b)
traverseA' f (Arr sh a) = Arr sh <$> traverseV f a

traverseV :: (V.Vector v a, V.Vector v b, Applicative f) => (a -> f b) -> v a -> f (v b)
traverseV f xs =   -- copied from VB.Vector Traversable impl
  let !n = V.length xs
  in V.fromListN n <$> traverse f (V.toList xs)

fmapArr' :: (L a, L b, Vec a ~ Vec b) => (a->b) -> Arr a -> Arr b
fmapArr' f (Arr sh a) = Arr sh (V.map f a)

fmapArr :: (L a, L b) => (a->b) -> Arr a -> Arr b
fmapArr f = coerce . traverseA (Identity . f)

tfmapb2 :: (Applicative f, L c)
        => (forall a b. (L a, L b, L c) => Arr a -> Arr b -> f (Arr c))
        -> Val -> Val -> f Val
tfmapb2 f a b = f `tap` a `tfmapb` b

tzip :: Functor f => (forall a. L a => Arr a -> Arr a -> f (Arr a)) -> Val -> Val -> f Val
tzip f = tagree (fmap atoval .: f)

tzipb :: L b => Functor f => (forall a. L a => Arr a -> Arr a -> f (Arr b)) -> Val -> Val -> f Val
tzipb f = tagree (fmap atoval .: f)

tagree :: (forall a. L a => Arr a -> Arr a -> b) -> Val -> Val -> b
tagree f (Ints    a) (Ints    b) = f a b
tagree f (Ints    a) (Nums    b) = f (fmapArr toRational a) b
tagree f (Nums    a) (Ints    b) = f a (fmapArr toRational b)
tagree f (Nums    a) (Nums    b) = f a b
tagree f (Chars   a) (Chars   b) = f a b
tagree f (Symbols a) (Symbols b) = f a b
tagree f (Paths   a) (Paths   b) = f a b
tagree f (Elems   a) (Elems   b) = f a b
tagree f a b = on f asElems a b

agreeElem :: (forall a. L a => a -> a -> b) -> Elem -> Elem -> b
agreeElem f (ENum    x) (ENum    y) = f x y
agreeElem f (EChar   x) (EChar   y) = f x y
agreeElem f (ESymbol x) (ESymbol y) = f x y
agreeElem f (EPath   x) (EPath   y) = f x y
agreeElem f x y = on f ltoelem x y

-- this probably shouldn't exist. i haven't made my mind up on it
spec :: forall b c. L b => (forall a. L a => a -> c) -> b -> c
spec f = go f . ltoelem
  where go :: (forall a. L a => a -> c) -> Elem -> c
        go f (ENum    x) = f x
        go f (EChar   x) = f x
        go f (ESymbol x) = f x
        go f (EPath   x) = f x
        go f x           = f x

agree :: (L c, L d) =>
         (forall a. L a => a -> a -> b) ->
         c -> d -> b
agree f a b = agreeElem f (ltoelem a) (ltoelem b)

firstCell :: Val -> Maybe Val
firstCell = tfmap firstCellL

firstCellL :: Arr a -> Maybe (Arr a)
firstCellL (Arr (_ : sh) a) = Just (Arr sh (V.take (axesSize sh) a))
firstCellL (Arr [] _) = Nothing

--unconsCell :: Val -> Maybe (Val, Val)
--unconsCell (Arr (Ixd n : sh) a) = Just (on bimap Arr sh (Ixd (n-1) : sh)
--                                                     (V.splitAt (axesSize sh) a))
----unconsCell (Arr (Ixd n : sh) a) = Just (on (,) Arr (sh, Ixd (n-1) : sh) <<*>> V.splitAt (axesSize sh) a)
--unconsCell (Quot (a:as)) = Just (Atom a, Quot as)
--unconsCell _ = Nothing

cellAt :: L a => [Axis] -> Vec a -> Int -> Arr a
cellAt sh a n = Arr sh (V.slice (n*size) size a) where size = axesSize sh

rankRel :: (Applicative m, L a, L b) => Int -> [Axis] -> (Arr a -> m (Vec b)) -> Arr a -> m (Arr b)
rankRel r newsh f (Arr sh a) =
  Arr (lsh <> newsh) . V.concat <$> traverse (f . cellAt rsh a) [0..axesSize lsh]
  where (lsh,rsh) = splitAt r sh

rankNumber :: Arr a -> Int -> Int
rankNumber (Arr (axesSize -> len) _) r | r < 0     = min 0 (len + r)
                                         | otherwise = max len r

rank :: (Applicative m, L a, L b) => Int -> [Axis] -> (Arr a -> m (Vec b)) -> Arr a -> m (Arr b)
rank r newsh f a = rankRel (rankNumber a r) newsh f a


leadingAxis :: [Axis] -> [Axis] -> Maybe ([Axis], [Int], [Int])
leadingAxis sh sh' = match sh sh'
  where
    trim nsh i i' = Just (nsh, take (axesSize nsh) i, take (axesSize nsh) i')
    match (x:xs) (y:ys) | x == y    = match xs ys
                        | otherwise = Nothing
    match [] [] = trim sh  [0..]                              [0..]
    match x  [] = trim sh  [0..]                              ([0..] >>= replicate (axesSize x))
    match [] y  = trim sh' ([0..] >>= replicate (axesSize y)) [0..]

birankRel :: (Applicative m, L a, L b, L c)
           => Int -> Int
           -> [Axis] -> (Arr a -> Arr b -> m (Vec c))
           -> Arr a -> Arr b -> Maybe (m (Arr c))
birankRel r r' nrsh f (Arr sh a) (Arr sh' b) =
  leadingAxis lsh lsh' <&> \(nlsh, i, i')->
    Arr (nlsh <> nrsh) . V.concat <$> zipWithM (\j j'-> f (cellAt rsh a j) (cellAt rsh' b j')) i i'
  where (lsh ,rsh ) = splitAt r  sh
        (lsh',rsh') = splitAt r' sh'

tap2 :: (forall a b. (L a, L b) => Arr a -> Arr b -> c) -> Val -> Val -> c
tap2 f = flip (tap (flip (tap f)))

birank :: Applicative m
       => Int -> Int
       -> [Axis] -> (Val -> Val -> m (VB.Vector Elem))
       -> Val -> Val -> Maybe (m Val)
birank r r' newsh f a b =
  fmap atoval <$> tap2 (birankL r r' newsh \x y -> f (atoval x) (atoval y)) a b

birankL :: (Applicative m, L a, L b, L c)
        => Int -> Int
        -> [Axis] -> (Arr a -> Arr b -> m (Vec c))
        -> Arr a -> Arr b -> Maybe (m (Arr c))
birankL r r' newsh f a b = birankRel (rankNumber a r) (rankNumber b r') newsh f a b

-- where `lazip1 f` <-> `lazip [] (V.singleton .: f)`
lazip1 :: (Applicative m, L a, L b, L c)
       => (a -> b -> m c)
       -> Arr a -> Arr b -> Maybe (m (Arr c))
lazip1 f (Arr sh a) (Arr sh' b) =
  leadingAxis sh sh' <&> \(nlsh, i, i')->
    Arr nlsh . V.fromListN (axesSize nlsh) <$> zipWithM (\j j'-> f (a V.! j) (b V.! j')) i i'

lazip :: (Applicative m, L a, L b, L c)
      => [Axis] -> (a -> b -> m (Vec c))
      -> Arr a -> Arr b -> Maybe (m (Arr c))
lazip nrsh f (Arr sh a) (Arr sh' b) =
  leadingAxis sh sh' <&> \(nlsh, i, i')->
    Arr (nlsh <> nrsh) . V.concat <$> zipWithM (\j j'-> f (a V.! j) (b V.! j')) i i'

scalar :: L b => Applicative m => (forall a. L a => a -> m b) -> Val -> m Val
scalar f (Elems a) = Elems <$> traverseA go a
  where go (EBox a) = EBox <$> scalar f a
        go a        = ltoelem <$> f a
scalar f a = tfmapb (traverseA f) a

biscalar :: forall m c . Applicative m => L c
         => m Val   -- mismatched axes error value
         -> (forall a b. (L a, L b) => a -> b -> m c)
         -> Val -> Val -> m Val
biscalar err f (Elems a) (Elems b) =
  maybe err (fmap atoval) (lazip1 f' a b)
  where f' :: Elem -> Elem -> m Elem
        f' (EBox as) (EBox bs) = EBox <$> biscalar err f as bs
        f' (EBox as) b         = EBox <$> scalar (  `f` b) as
        f' a         (EBox bs) = EBox <$> scalar (a `f`  ) bs
        f' a         b         = ltoelem <$> f a b
biscalar err f (Elems a) b =
  maybe err (fmap atoval) (tap (lazip1 f' a) b)
  where f' :: L a => Elem -> a -> m Elem
        f' (EBox as) b = EBox <$> scalar (`f` b) as
        f' a         b = ltoelem <$> f a b
biscalar err f a (Elems b) = --biscalar err (flip f) (Elems b) a
  maybe err (fmap atoval) (tap (lazip1 f' b) a)
  where f' :: L a => Elem -> a -> m Elem
        f' (EBox bs) a = EBox <$> scalar (a `f`) bs
        f' b         a = ltoelem <$> f a b
biscalar err f a b = fromMaybe err (coerce (tfmapb2 (Compose .: lazip1 f) a b))


pushLabel :: L a => Val -> Elem -> Vec a -> Val
--pushLabel a n el = atoval (pushLabelL (valtoart a) n el)
pushLabel a n el = coerce (tzip go a (atoval (Arr [] el)))
  where
    go :: forall a. L a => Arr a -> Arr a -> Identity (Arr a)
    go a (Arr _ el) = Identity (pushLabelL a n el)

pushLabelL :: L a => Arr a -> Elem -> Vec a -> Arr a
pushLabelL (Arr shp@(Nmd (Bivector nms ei) : sh') v) n el =
  assert (V.length el == axesSize sh')
  case HM.lookup n ei of
    Just x  -> Arr shp (V.modify (flip V.copy el . VM.slice (x * axesSize sh') (axesSize sh')) v)
    Nothing -> Arr (Nmd (Bivector (V.snoc nms n)
                                  (HM.insert n (V.length nms) ei)) : sh')
                    (v V.++ el)
pushLabelL _ _ _ = undefined

mergeRecords :: Bivector Elem -> Bivector Elem -> [Axis] -> Vec Elem -> Vec Elem -> Val
mergeRecords left (Bivector nms' _) sh a b =
  foldl (uncurry . pushLabel)
        (Elems (Arr (Nmd left : sh) a))
        (zip (V.toList nms') (vchunksOf (axesSize sh) b))

mergeRecordsL :: L a => Bivector Elem -> Bivector Elem -> [Axis] -> Vec a -> Vec a -> Arr a
mergeRecordsL left (Bivector nms' _) sh a b =
  foldl (uncurry . pushLabelL)
        (Arr (Nmd left : sh) a)
        (zip (V.toList nms') (vchunksOf (axesSize sh) b))


isScalar :: Elem -> Bool
isScalar (EBox _) = True
isScalar _        = False

enclose :: Val -> Val
enclose x = Elems (Atom (asElem x))

asElem :: Val -> Elem
asElem c@(Elems (Atom _)) = EBox c
asElem a = tap go a
  where go (Atom x) = ltoelem x
        go a = EBox (atoval a)

unwrap :: Elem -> Val
unwrap (EBox a) = a
unwrap a        = Elems (Atom a)

isTrue :: L a => a -> Maybe Bool
isTrue x = (0 /=) <$> toRat x
{-# INLINE isTrue #-}

asAxes :: Val -> Maybe [Axis]
asAxes = tap asAxesL

asAxesL :: L a => Arr a -> Maybe [Axis]
asAxesL (Atom x) = pure <$> asAxis (ltoelem x)
asAxesL (Arr [Ixd n] xs) = assert (V.length xs == n)
                           do traverse (asAxis.ltoelem) (V.toList xs)
asAxesL _ = Nothing

asAxis :: Elem -> Maybe Axis
asAxis (ENum x) = Just (Ixd (fromEnum x))
asAxis (EBox (Elems (Arr [Ixd n] xs))) = assert (length xs == n)$ Just (Names xs)
asAxis _ = Nothing


reshape :: [Axis] -> Val -> Val
reshape sh' = tmapor (reshapel sh') (q sh')
  where q [Ixd size] l = Quot  (take size (cycle l))
        q sh'        l = Elems (Arr sh' (V.fromListN (axesSize sh') (cycle l)))

reshapel :: [Axis] -> Arr a -> Arr a
reshapel sh' (Arr sh a) = Arr sh' (V.concat (replicate d a <> [V.take m a]))
  where (d,m) = on divMod axesSize sh' sh

deshape :: Val -> Val
deshape = tmapq deshapel id

deshapel :: L a => Arr a -> Arr a
deshapel (Arr sh a) = Arr [Ixd (axesSize sh)] a

flattenToList :: L a => Arr a -> [a]
flattenToList (Arr sh a) = take (axesSize sh) (V.toList a)

forceQuot :: Val -> [Elem]
forceQuot = tapq (fmap ltoelem . flattenToList) id

asElems :: Val -> Arr Elem
asElems = tap (fmapArr ltoelem)

construct :: Val -> Val -> Maybe Val
construct (Quot a) b = Just (Quot (asElem b : a))
construct a b = tzip go a b
  where
    --go :: Arr a -> Arr a -> Maybe (Arr a)
    go (Atom a) (Atom b) = Just (pairl a b)
    go (Arr (Ixd n : sh) a) (Arr sh' b) | sh == sh' = Just (Arr (Ixd (n+1) : sh) (b V.++ a))
    go _ _ = Nothing
--construct (Arr (Ixd n : sh) a) (Arr' sh' b) | sh == sh' = Just (Arr (Ixd (n + 1) : sh) (b V.++ a))
--construct _ _ = Nothing

catenate :: Val -> Val -> Maybe Val
catenate (Quot a) (Quot b) = Just (Quot (a ++ b))
catenate a b = tzip go a b
  where
    go (Atom a) (Atom b) = Just (pairl a b)
    go (Arr (Ixd n : sh) a) (Arr (Ixd n' : sh') b) |sh==sh'= Just (Arr (Ixd (n + n') : sh) (a V.++ b))
    go (Arr (Ixd n : sh) a) (Arr           sh'  b) |sh==sh'= Just (Arr (Ixd (n + 1 ) : sh) (a V.++ b))
    go (Arr          sh  a) (Arr (Ixd n' : sh') b) |sh==sh'= Just (Arr (Ixd (1 + n') : sh) (a V.++ b))
    go (Arr (Nmd n : sh) a) (Arr (Nmd n' : sh') b) |sh==sh'= Just (mergeRecordsL n n' sh a b)
    go _ _ = Nothing

fitsIn :: Int -> Int -> Bool
fitsIn len n = n >= 0 && n < len

indexCell :: Int -> Val -> Maybe Val
indexCell n (Quot elems) = guard (n `fitsIn` length elems) $> Elems (Atom (elems !! n))
indexCell n x = tfmap (indexCellL n) x

indexCellL :: forall a. L a => Int -> Arr a -> Maybe (Arr a)
indexCellL n (Arr (ax : sh) a) = guard (n `fitsIn` axisLength ax) $> cellAt sh a n
indexCellL _ (Arr [] _) = Nothing

indexCellByName :: Elem -> Arr a -> Maybe (Arr a)
indexCellByName i (Arr (Nmd (Bivector _ ei) : sh) a) = cellAt sh a <$> HM.lookup i ei
indexCellByName _ _ = Nothing

indexElement :: [Either Int Elem] -> Val -> Maybe Elem
indexElement [Left n] (Quot a) = guard (n `fitsIn` length a) $> a !! n
indexElement is x = tap (fmap ltoelem . indexElementL is) x

indexElementL :: forall a. L a => [Either Int Elem] -> Arr a -> Maybe a
indexElementL is (Arr sh a) =
  guard (length sh == length is) >>
  zipWithM \cases
    (Ixd end)              (Left n) -> guard (n `fitsIn` end       ) $> n
    (Nmd (Bivector nms _)) (Left n) -> guard (n `fitsIn` length nms) $> n
    (Ixd _)                (Right _) -> Nothing
    (Nmd (Bivector _ ie))  (Right i) -> HM.lookup i ie
  sh is
  <&> \indices-> a V.! (sum . zipWith (*) indices . tail . scanr (*) 1 . map axisLength) sh

shortShowL :: L a => Arr a -> String
shortShowL (Atom a) = lshow a
shortShowL (Arr sh a) = "{" <> show sh <> "⍴" <> (V.toList a >>= (" " <>) . lshow) <> "}"

shortShow :: Val -> String
shortShow = tap shortShowL

axisToElem :: Axis -> Elem
axisToElem (Ixd n) = ENum (toRational n)
axisToElem (Names n) = EBox (vec n)

axesToVal :: [Axis] -> Val
axesToVal sh = if all isIxd sh then Ints (listl (fromIntegral . axisLength <$> sh))
                               else list (axisToElem <$> sh)
  where isIxd (Ixd _) = True
        isIxd (Nmd _) = False
