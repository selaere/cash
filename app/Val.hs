module Val where

import GHC.Generics (Generic)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Vector as VB
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Generic as V
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable (..))
import Parse (Ident)
import Data.Kind (Type)
import Data.Int (Int64)
import Data.Ratio (numerator, denominator)
import Data.Function (on)


infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

newtype Symbol = Symbol T.Text
  deriving (Eq, Show, Hashable)

data Elem
  = ENum Rational
  | ESymbol Symbol
  | EChar Char
  | EPath T.Text
  | EBox Val
  | ECmd Act
  deriving (Eq, Generic, Show)
instance Hashable Elem

data Axis = Ixd Int | Nmd (Bivector Elem)
  deriving Show


-- unrelated to the geometric algebra
-- (it's just a BIdirectional VECTOR)
data Bivector a = Hashable a => Bivector (VB.Vector a) (HM.HashMap a Int)

deriving instance Show a => Show (Bivector a)

bivector :: Hashable a => VB.Vector a -> Bivector a
bivector s = Bivector s (HM.fromList (zip (V.toList s) [0..]))


instance Eq Axis where
  Ixd n              == Ixd n'              = n == n'
  Nmd (Bivector v _) == Nmd (Bivector v' _) = v == v'
  _ == _ = False


pattern Names :: VB.Vector Elem -> Axis
pattern Names s <- Nmd (Bivector s _) where Names = Nmd . bivector

{-# COMPLETE Ixd, Names #-}


instance Hashable Axis where
  s `hashWithSalt` Ixd a   = s `hashWithSalt` (0::Int) `hashWithSalt` a
  s `hashWithSalt` Names a = s `hashWithSalt` (1::Int) `hashWithSalt` V.toList a

data Val = Ints    (Arr Int64)
         | Nums    (Arr Rational)
         | Chars   (Arr Char)
         | Symbols (Arr Symbol)
         | Paths   (Arr T.Text)
         | Elems   (Arr Elem)
         | Quot    [Elem]
  deriving (Eq, Generic, Show)


instance Hashable Val where
  s `hashWithSalt` Ints    a = s `hashWithSalt` (0::Int) `hashArr` a
  s `hashWithSalt` Nums    a = s `hashWithSalt` (1::Int) `hashArr` a
  s `hashWithSalt` Chars   a = s `hashWithSalt` (2::Int) `hashArr` a
  s `hashWithSalt` Symbols a = s `hashWithSalt` (3::Int) `hashArr` a
  s `hashWithSalt` Paths   a = s `hashWithSalt` (4::Int) `hashArr` a
  s `hashWithSalt` Elems   a = s `hashWithSalt` (5::Int) `hashArr` a
  s `hashWithSalt` Quot    a = s `hashWithSalt` (6::Int) `hashWithSalt` a

data Arr a = L a => Arr [Axis] (Vec a)

deriving instance Eq (Arr a)
deriving instance Show (Arr a)

hashArr :: Hashable a => Int -> Arr a -> Int
hashArr s (Arr sh a) = s `hashWithSalt` sh `hashWithSalt` V.toList a

data Output = Output T.Text
            | OutputRed T.Text
            
newtype Path = Path T.Text

class Effect e o | e -> o where
  doEffect :: e -> IO o
  effOut :: e -> Output

data Anything a = Anything (IO a) T.Text
instance Effect (Anything a) a where
  doEffect (Anything io _  ) = io
  effOut   (Anything _  lab) = Output lab

newtype ReadFile = ReadFile FilePath
instance Effect ReadFile T.Text where
  doEffect (ReadFile path) = TIO.readFile path
  effOut (ReadFile path) = Output (T.pack ("read file at "<>path))

class Error m where
  errAsVal :: m -> Val
  showErr :: m -> Output

class (Monad m) => CashMonad m where
  cashLog :: Output -> m ()
  cashError :: Error e => e -> m a
  effect :: Effect e o => e -> m o

data Act = Comb Fun [[Act]]
         | CombUnf Fun [[Act]]
         | Push Ident
         | Peek Ident
         | Pop Ident
         | Const Val
  deriving (Eq, Generic, Show)

instance Hashable Act
--                 | QuotRef [Val]
data Def = Def Fun Int
  deriving (Eq, Generic, Show)

--data Fun = Fun (forall m. CashMonad m => [Val] -> m [Val])
data Fun = FAdd | FSub | FMul | FDiv | FNot | FCat | FCons | FReshape | FShape
         | FDrop | FDup | FSwap | FRot | FOver | FShow
-- | FQuot [Act]
  deriving (Eq, Generic, Show)
instance Hashable Fun

data ValErr = NotANumber Elem | NotANumber2 Elem Elem
  deriving (Eq, Show)

instance Error ValErr where
  showErr x = Output (T.pack (show x))
  errAsVal = undefined


type Vec a = VecL a a
class (V.Vector (VecL a) a, Eq a, Show a, Eq (Vec a), Show (Vec a)) => L a where

  type VecL a :: Type -> Type
  ltoelem :: L a => a -> Elem
  atoval  :: L a => Arr a -> Val
  lshow :: L a => a -> String

  math :: (L a, CashMonad m) => (forall x y. (Num x, Num y) => x -> m y) -> a -> m a
  math _ a = cashError (NotANumber (ltoelem a))
  math2 :: (L a, CashMonad m) => (forall x y z. (Num x, Num y, Num z) => x -> y -> m z) -> a -> a -> m a
  math2 _ a b = cashError (on NotANumber2 ltoelem a b)
  mathRat :: (L a, CashMonad m) => (Rational -> m Rational) -> a -> m Rational
  mathRat _ a = cashError (NotANumber (ltoelem a))
  mathRat2 :: (L a, CashMonad m) => (Rational -> Rational -> m Rational) -> a -> a -> m Rational
  mathRat2 _ a b = cashError (on NotANumber2 ltoelem a b)

instance L Elem where
  type VecL Elem = VB.Vector
  ltoelem  = id
  atoval   = Elems
  lshow (ENum a) = lshow a
  lshow a        = show a

instance L Int64 where
  type VecL Int64 = VU.Vector
  ltoelem  = ENum . toRational
  atoval   = Ints
  lshow    = show
  math     f = f
  math2    f = f
  mathRat  f = f . toRational
  mathRat2 f = on f toRational

instance L Rational where
  type VecL Rational = VB.Vector
  ltoelem  = ENum
  atoval   = Nums
  lshow x  | d == 1 = show n
           | otherwise = show n <> "/" <> show d
    where n = numerator x ; d = denominator x
  math     f = f
  math2    f = f
  mathRat  f = f
  mathRat2 f = f

instance L Char where
  type VecL Char = VU.Vector
  ltoelem  = EChar
  atoval   = Chars
  lshow    = show
  math  f = fmap toEnum .  f  . fromEnum
  math2 f = fmap toEnum .: on f fromEnum

instance L Symbol where
  type VecL Symbol = VB.Vector
  ltoelem  = ESymbol
  atoval   = Symbols
  lshow    = show

instance L T.Text where
  type VecL T.Text = VB.Vector
  ltoelem  = EPath
  atoval   = Paths
  lshow    = show
