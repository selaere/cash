module Arr where

import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import qualified Data.HashMap.Strict as HM
import Data.Bifunctor (bimap)
import Data.List.Split (chunksOf)
import Control.Exception (assert)
import Data.Function (on)
import Control.Monad (guard, zipWithM)
import Data.Functor (($>), (<&>))
import Val (Val(..), Axis(..), pattern Names, Elem(EBox, ENum, EChar), Bivector(..))
import Data.Maybe (fromMaybe)
import Data.Ratio (numerator, denominator)


infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

onlyArr :: Val -> Val
onlyArr a@(Arr _ _) = a
onlyArr (Quot elems) = list elems

-- for when i dont want to bother to handle the Quot case
pattern Arr' :: [Axis] -> V.Vector Elem -> Val
pattern Arr' sh a <- (onlyArr -> Arr sh a)
{-# COMPLETE Arr' #-}


pattern Atom :: Elem -> Val
pattern Atom a <- Arr [] (V.head -> a) where Atom a = Arr [] (V.singleton a)

list :: [Elem] -> Val
list (V.fromList -> elems) = Arr [Ixd (V.length elems)] elems

shape :: Val -> [Axis]
shape (Arr sh _) = sh
shape (Quot elems) = [Ixd (length elems)]

axisLength :: Axis -> Int
axisLength (Ixd l) = l
axisLength (Names ie) = length ie

axesSize :: [Axis] -> Int
axesSize = product . map axisLength

singleton :: Elem -> Val
singleton a = Arr [Ixd 1] (V.fromList [a])

pair :: Elem -> Elem -> Val
pair a b = Arr [Ixd 2] (V.fromList [a,b])

vchunksOf :: Int -> V.Vector a -> [V.Vector a]
vchunksOf i v = V.fromListN i <$> chunksOf i (V.toList v)

firstCell :: Val -> Maybe Val
firstCell (Arr (_ : sh) a) = Just (Arr sh (V.take (axesSize sh) a))
firstCell (Arr [] _) = Nothing
firstCell (Quot (a:_)) = Just (Atom a)
firstCell (Quot []) = Nothing

unconsCell :: Val -> Maybe (Val, Val)
unconsCell (Arr (Ixd n : sh) a) = Just (on bimap Arr sh (Ixd (n-1) : sh)
                                                     (V.splitAt (axesSize sh) a))
--unconsCell (Arr (Ixd n : sh) a) = Just (on (,) Arr (sh, Ixd (n-1) : sh) <<*>> V.splitAt (axesSize sh) a)
unconsCell (Quot (a:as)) = Just (Atom a, Quot as)
unconsCell _ = Nothing

cellAt :: [Axis] -> V.Vector Elem -> Int -> Val
cellAt sh a n = Arr sh (V.slice (n*size) size a) where size = axesSize sh

rankRel :: Applicative m => Int -> [Axis] -> (Val -> m (V.Vector Elem)) -> Val -> m Val
rankRel r newsh f (Arr' sh a) =
  Arr (lsh <> newsh) . V.concat <$> traverse (f . cellAt rsh a) [0..axesSize lsh]
  where (lsh,rsh) = splitAt r sh

rankNumber :: Val -> Int -> Int
rankNumber (shape -> axesSize -> len) r | r < 0     = min 0 (len + r)
                                        | otherwise = max len r

rank :: Applicative m => Int -> [Axis] -> (Val -> m (V.Vector Elem)) -> Val -> m Val
rank r newsh f a = rankRel (rankNumber a r) newsh f a

leadingAxis :: [Axis] -> [Axis] -> Maybe ([Axis], [Int], [Int])
leadingAxis sh sh' = match sh sh'
  where
    trim nsh i i' = Just (nsh, take (axesSize nsh) i, take (axesSize nsh) i')
    match (x:xs) (y:ys) | x == y    = match xs ys
                        | otherwise = Nothing
    match [] [] = trim sh  [0..]             [0..]
    match x  [] = trim sh  [0, axesSize x..] [0..]
    match [] y  = trim sh' [0..]             [0, axesSize y..]

birankRel :: Applicative m
          => Int -> Int
          -> [Axis] -> (Val -> Val -> m (V.Vector Elem))
          -> Val -> Val -> Maybe (m Val)
birankRel r r' nrsh f (Arr' sh a) (Arr' sh' b) =
  leadingAxis lsh lsh' <&> \(nlsh, i, i')->
    Arr (nlsh <> nrsh) . V.concat <$> zipWithM (\j j'-> f (cellAt rsh a j) (cellAt rsh' b j')) i i'
  where (lsh ,rsh ) = splitAt r  sh
        (lsh',rsh') = splitAt r' sh'

birank :: Applicative m
       => Int -> Int
       -> [Axis] -> (Val -> Val -> m (V.Vector Elem))
       -> Val -> Val -> Maybe (m Val)
birank r r' newsh f a b = birankRel (rankNumber a r) (rankNumber b r') newsh f a b


lazip :: Applicative m
      => [Axis] -> (Elem -> Elem -> m (V.Vector Elem))
      -> Val -> Val -> Maybe (m Val)
lazip nrsh f (Arr' sh a) (Arr' sh' b) =
  leadingAxis sh sh' <&> \(nlsh, i, i')->
    Arr (nlsh <> nrsh) . V.concat <$> zipWithM (\j j'-> f (a V.! j) (b V.! j')) i i'

scalar :: Applicative m => (Elem -> m Elem) -> Val -> m Val
scalar f = elements f'
  where f' (EBox as) = EBox <$> scalar f as
        f' a' = f a'

biscalar :: Applicative m
         => m Val   -- mismatched axes error value
         -> (Elem -> Elem -> m Elem)
         -> Val -> Val -> m Val
biscalar err f = fromMaybe err .: lazip [] (fmap V.singleton .: f')
  where
    --f' :: Elem -> Elem -> m Elem
    f' (EBox as) (EBox bs) = EBox <$> biscalar err f as bs
    f' (EBox as) b'        = EBox <$> scalar (   `f'` b') as
    f' a'        (EBox bs) = EBox <$> scalar (a' `f'`   ) bs
    f' a'        b'        = f a' b'

elements :: Applicative m => (Elem -> m Elem) -> Val -> m Val
elements f (Arr sh a) = Arr sh <$> traverse f a
elements f (Quot a) = Quot <$> traverse f a


pushLabel :: Val -> Elem -> V.Vector Elem -> Val
pushLabel (Arr shp@(Nmd (Bivector nms ei) : sh') v) n el =
  assert (V.length el == axesSize sh')
  case HM.lookup n ei of
    Just x  -> Arr shp (V.modify (flip V.copy el . VM.slice (x * axesSize sh') (axesSize sh')) v)
    Nothing -> Arr (Nmd (Bivector (V.snoc nms n)
                                  (HM.insert n (V.length nms) ei)) : sh')
                   (v V.++ el)
pushLabel _ _ _ = undefined

mergeRecords :: Bivector Elem -> Bivector Elem -> [Axis] -> V.Vector Elem -> V.Vector Elem -> Val
mergeRecords left (Bivector nms' _) sh a b =
  foldl (uncurry . pushLabel)
        (Arr (Nmd left : sh) a)
        (zip (V.toList nms') (vchunksOf (axesSize sh) b))

isScalar :: Elem -> Bool
isScalar (EBox _) = True
isScalar _        = False

enclose :: Val -> Val
enclose = Atom . asElem

asElem :: Val -> Elem
asElem c@(Atom (EBox _)) = EBox c
asElem (Atom e)          = e
asElem c                 = EBox c

unwrap :: Elem -> Val
unwrap (EBox a) = a
unwrap a        = Atom a

asAxes :: Val -> Maybe [Axis]
asAxes (Atom x) = pure <$> asAxis x
asAxes (Arr' [Ixd n] xs) = assert (length xs == n)$ traverse asAxis (V.toList xs)
asAxes _ = Nothing

asAxis :: Elem -> Maybe Axis
asAxis (ENum x) = Just (Ixd (fromEnum x))
asAxis (EBox (Arr' [Ixd n] xs)) = assert (length xs == n)$ Just (Names xs)
asAxis _ = Nothing

reshape :: [Axis] -> Val -> Val
reshape sh' (Arr sh a) = Arr sh' (V.concat (replicate d a <> [V.take m a]))
  where (d,m) = on divMod axesSize sh' sh
reshape [Ixd size] (Quot l) = Quot (take size (cycle l))
reshape sh'@(axesSize -> size) (Quot l) = Arr sh' (V.fromListN size (cycle l))

deshape :: Val -> Val
deshape (Arr sh a) = Arr [Ixd (axesSize sh)] a
deshape (Quot a)   = Quot a

construct :: Val -> Val -> Maybe Val
construct (Quot a) b = Just (Quot (asElem b : a))
construct (Atom a) (Atom b) = Just (pair b a)
construct (Arr (Ixd n : sh) a) (Arr' sh' b) | sh == sh' = Just (Arr (Ixd (n + 1) : sh) (b V.++ a))
construct _ _ = Nothing

catenate :: Val -> Val -> Maybe Val
catenate (Quot a) (Quot b) = Just (Quot (a ++ b))
catenate (Atom a) (Atom b) = Just (pair a b)
catenate (Arr' (Ixd n : sh) a) (Arr' (Ixd n' : sh') b) | sh == sh' = Just (Arr (Ixd (n + n') : sh) (a V.++ b))
catenate (Arr' (Ixd n : sh) a) (Arr'           sh'  b) | sh == sh' = Just (Arr (Ixd (n + 1 ) : sh) (a V.++ b))
catenate (Arr'          sh  a) (Arr' (Ixd n' : sh') b) | sh == sh' = Just (Arr (Ixd (1 + n') : sh) (a V.++ b))
catenate (Arr' (Nmd n : sh) a) (Arr' (Nmd n' : sh') b) | sh == sh' = Just (mergeRecords n n' sh a b)
catenate _ _ = Nothing

fitsIn :: Int -> Int -> Bool
fitsIn len n = n >= 0 && n < len

indexCell :: Int -> Val -> Maybe Val
indexCell n (Arr (ax : sh) a) | n `fitsIn` axisLength ax = Just (cellAt sh a n)
                              | otherwise                = Nothing
indexCell _ (Arr [] _) = Nothing
indexCell n (Quot elems) | n `fitsIn` length elems = Just (Atom (elems !! n))
                         | otherwise               = Nothing

indexCellByName :: Elem -> Val -> Maybe Val
indexCellByName i (Arr (Nmd (Bivector _ ei) : sh) a) = cellAt sh a <$> HM.lookup i ei
indexCellByName _ _ = Nothing

indexElement :: [Either Int Elem] -> Val -> Maybe Elem
indexElement is (Arr sh a) | length sh == length is =
  zipWithM \cases
    (Ixd end)              (Left n) -> guard (n `fitsIn` end       ) $> n
    (Nmd (Bivector nms _)) (Left n) -> guard (n `fitsIn` length nms) $> n
    (Ixd _)                (Right _) -> Nothing
    (Nmd (Bivector _ ie))  (Right i) -> HM.lookup i ie
  sh is
  <&> \indices-> a V.! (sum . zipWith (*) indices . tail . scanr (*) 1 . map axisLength) sh
indexElement [Left n] (Quot a) = guard (n `fitsIn` length a) $> a !! n
indexElement _ _ = Nothing


shortShow :: Val -> String
shortShow (Atom (ENum x)) | d == 1 = show n
                   | otherwise = show n <> "/" <> show d
  where n = numerator x ; d = denominator x
shortShow (Atom (EChar x)) = "'" <> show x <> "'"
shortShow x = show x