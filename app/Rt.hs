module Rt where
import Parse (Obj(..), Ident)
import Val (Val(..), CashMonad(..), Output(..), Error(..), Effect(..), Def(..), Elem (..), Act(..), Fun)
import Arr (pattern Atom, asElem, list)
import qualified Control.Monad.Trans.State as S
import qualified Data.HashMap.Strict as HM
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Data.Text as T
import qualified Val
import Control.Applicative (empty)
import Data.Functor ((<&>))
import Data.Bifunctor (first)
import Data.List (singleton)
import Prim (exec)
import Control.Lens ((%=), Traversal', use, At (at), (.=))
import Data.Maybe (fromMaybe)

data RtState = RtState { stacks :: HM.HashMap Ident [Val]
                       , defs   :: HM.HashMap Ident Def }

defaultRtState :: RtState
defaultRtState = RtState { stacks = HM.empty, defs = primitives }

primitives :: HM.HashMap Ident Def
primitives = HM.fromList $ map (\(x,y,z) -> (T.pack x, Def y z))
  [ ("+", Val.FAdd,     0)
  , ("-", Val.FSub,     0)
  , ("*", Val.FMul,     0)
  , ("/", Val.FDiv,     0)
  , ("~", Val.FNeg,     0)
  , ("`", Val.FCat,     0)
  , ("^", Val.FCons,    0)
  , ("E", Val.FReshape, 0)
  , ("'", Val.FDrop,    0)
  , (".", Val.FDup,     0)
  , (",", Val.FSwap,    0)
  , (";", Val.FRot,     0)
  , (":", Val.FOver,    0)
  , ("\"",Val.FShow,    0)
  ]

_stacks :: Traversal' RtState (HM.HashMap Ident [Val])
_defs   :: Traversal' RtState (HM.HashMap Ident Def)
_stacks f r = f (stacks r) <&> \x -> r {stacks = x}
_defs   f r = f (defs   r) <&> \x -> r {defs   = x}


type RtM = S.StateT RtState IO

instance CashMonad RtM where
  cashLog (Output x) = liftIO (print x)
  cashLog (OutputRed x) = liftIO (print (T.pack "<red>" <> x <> T.pack "</red>"))
  cashError err = cashLog (showErr err) >> empty
  effect = liftIO . doEffect


data RtErr
  = CmdNotFound Ident
  | EmptyStream
  | PatNotFound Ident
  | UnexpectedQuot
  | VarNotThere Ident
  | UnfCombinator Fun [[Act]]
  deriving (Eq, Show)


instance Error RtErr where
  -- showErr (CmdNotFound i) = Output (i<>T.pack " not found")
  -- showErr EmptyStream     = Output (T.pack "empty stream")
  -- showErr (PatNotFound i) = Output (i<>T.pack "[ not found")
  -- showErr UnexpectedQuot = Output (T.pack "unexpected quotation")
  -- showErr (VarNotThere i) = Output (T.pack"variable "<>i<>T.pack " not found")
  -- showErr (UnfCombinator) = 
  showErr x = Output (T.pack (show x))
  errAsVal = undefined

--meow :: [Obj] -> [Val] -> RtM [Val]
--meow [] stk = pure stk



placeholderActsToVal :: [Act] -> Val
placeholderActsToVal = Quot . (>>= conv)
  where conv :: Act -> [Elem]
        conv (Comb c a) = (EBox . placeholderActsToVal <$> a) <> [ECmd (Comb c [])]
        conv (CombUnf c a) = conv (Comb c a) -- trolled
        conv (Const a) = [asElem a]
        conv a = [ECmd a]

doAct :: Act -> [Val] -> RtM [Val]
doAct (Comb    fun acts) xs = exec fun (map placeholderActsToVal acts ++ xs)
doAct (CombUnf fun acts) _s = cashError (UnfCombinator fun acts)
doAct (Push var) (x:xs) = do _stacks . at var %= Just . (x:) . fromMaybe [] ; return xs
doAct (Push _ar) [] = undefined
doAct (Peek var) xs =
  use (_stacks.at var) >>= \case
    Just []    -> cashError (VarNotThere var)
    Just (v:_) -> pure (v:xs)
    Nothing    -> cashError (VarNotThere var)
doAct (Pop  var) xs =
  use (_stacks.at var) >>= \case
    Just []      -> cashError (VarNotThere var)
    Just [v]     -> do _stacks.at var .= Nothing ; return (v:xs)
    Just (v:vs)  -> do _stacks.at var .= Just vs ; return (v:xs)
    Nothing      -> cashError (VarNotThere var)
doAct (Const x) xs = pure (x:xs)


run :: [Obj] -> [Val] -> RtM [Val]
run [] s = return s
run os s = use _defs >>= \d-> case cutAct d os of
  Left err         -> cashError err
  Right (act, os') -> doAct act s >>= run os'


runWith :: RtState -> [Obj] -> [Val] -> IO ([Val], RtState)
runWith r os s = S.runStateT (run os s) r


cutQuot :: HM.HashMap Ident Def -> [Obj] -> Either RtErr ([Act], [Obj])
cutQuot defs (QuotF   a : os) = (,os) <$> readQuot defs a
cutQuot defs (QuotUnf a : os) = (,os) <$> readQuot defs a -- todo do something different
cutQuot defs a                = first singleton <$> cutAct defs a

cutAct :: HM.HashMap Ident Def -> [Obj] -> Either RtErr (Act, [Obj])
cutAct defs (Cmd ident : os) =
  case HM.lookup ident defs of
    Just (Def call arity) -> readQuotN defs ([], os) arity <&> first (Comb call)
    Nothing               -> Left (CmdNotFound ident)
cutAct _efs (Numlit i : os)   = Right (Const (Atom (ENum (toRational i))), os)
cutAct _efs (LitLabel l : os) = Right (Const (Atom (ESymbol l)), os)
cutAct defs (QuotF a : os) = (,os) . Const . placeholderActsToVal <$> readQuot defs a
cutAct defs (QuotUnf a : os) = cutAct defs (QuotF a : os)
cutAct _efs (Literal i t : os) | T.null i = Right (Const (list (EChar <$> T.unpack t)), os)
                               | otherwise= Left (PatNotFound i)
cutAct _efs (OPush i : os) = Right (Push i, os)
cutAct _efs (OPeek i : os) = Right (Peek i, os)
cutAct _efs (OPop  i : os) = Right (Pop  i, os)

cutAct _efs [] = Left EmptyStream

readQuot :: HM.HashMap Ident Def -> [Obj] -> Either RtErr [Act]
readQuot _    [] = Right []
readQuot defs a = cutAct defs a >>= \(c, xs) -> (c:) <$> readQuot defs xs


readQuotN :: HM.HashMap Ident Def -> ([[Act]], [Obj]) -> Int -> Either RtErr ([[Act]], [Obj])
readQuotN _    (cs, os) 0 = Right (cs, os)
readQuotN defs (cs, os) k = cutQuot defs os >>= \(c, os')-> readQuotN defs (c:cs, os') (k-1)

