module Val where

import GHC.Generics (Generic)
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified Data.Vector as V
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable (..))
import Parse (Ident)



data Elem
  = ENum Rational
  | ESymbol Text.Text
  | EChar Char
  | EPath Text.Text
  | EBox Val
  | ECmd Act
  deriving (Eq, Generic, Show)
instance Hashable Elem




data Axis = Ixd Int | Nmd (Bivector Elem)
  deriving Show


-- unrelated to the geometric algebra
-- (it's just a BIdirectional VECTOR)
data Bivector a = Hashable a => Bivector (V.Vector a) (HM.HashMap a Int)

deriving instance Show a => Show (Bivector a)

bivector :: Hashable a => V.Vector a -> Bivector a
bivector s = Bivector s (HM.fromList (zip (V.toList s) [0..]))


instance Eq Axis where
  Ixd n              == Ixd n'              = n == n'
  Nmd (Bivector v _) == Nmd (Bivector v' _) = v == v'
  _ == _ = False


pattern Names :: V.Vector Elem -> Axis
pattern Names s <- Nmd (Bivector s _) where Names = Nmd . bivector

{-# COMPLETE Ixd, Names #-}


instance Hashable Axis where
  s `hashWithSalt` Ixd a   = s `hashWithSalt` (0::Int) `hashWithSalt` a
  s `hashWithSalt` Names a = s `hashWithSalt` (1::Int) `hashWithSalt` V.toList a

instance Hashable Val where
  s `hashWithSalt` Arr a ve = s `hashWithSalt` (0::Int) `hashWithSalt` a `hashWithSalt` V.toList ve
  s `hashWithSalt` Quot e   = s `hashWithSalt` (1::Int) `hashWithSalt` e

data Val = Arr [Axis] (V.Vector Elem) | Quot [Elem]
  deriving (Eq, Generic, Show)

data Output = Output Text.Text
            | OutputRed Text.Text
            
newtype Path = Path Text.Text

class Effect e o | e -> o where
  doEffect :: e -> IO o
  effOut :: e -> Output

data Anything a = Anything (IO a) Text.Text
instance Effect (Anything a) a where
  doEffect (Anything io _  ) = io
  effOut   (Anything _  lab) = Output lab

newtype ReadFile = ReadFile FilePath
instance Effect ReadFile Text.Text where
  doEffect (ReadFile path) = TIO.readFile path
  effOut (ReadFile path) = Output (Text.pack ("read file at "<>path))

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
data Fun = FAdd | FSub | FMul | FDiv | FNeg | FCat | FCons | FReshape 
         | FDrop | FDup | FSwap | FRot | FOver | FShow
-- | FQuot [Act]
  deriving (Eq, Generic, Show)
instance Hashable Fun
