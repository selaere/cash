module Rt where
import Parse (Tok(..), Obj(..), Ident, Position(..), formatLine)
import Val (Val(..), CashMonad(..), Output(..), Error(..), Effect(..), Def(..), Elem(..), Act(..), Fun, assertInt)
import Arr (pattern Atom, asElem, list, unwrap, listl)
import qualified Control.Monad.Trans.State as S
import qualified Data.HashMap.Strict as HM
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Data.Text as T
import qualified Val
import Data.Functor ((<&>))
import Data.Bifunctor (first)
import Data.List (singleton)
import Prim (exec)
import Control.Lens ((%=), Traversal', use, at, (.=))
import Data.Maybe (fromMaybe)
import System.Exit (exitFailure)
import Control.Monad (foldM)

data RtState = RtState { stacks :: HM.HashMap Ident [Val]
                       , defs   :: HM.HashMap Ident Def
                       , sources:: HM.HashMap FilePath T.Text }

defaultRtState :: RtState
defaultRtState = RtState { stacks = HM.empty, defs = primitives, sources = HM.empty }

primitives :: HM.HashMap Ident Def
primitives = (HM.fromList . map \(x,y,z) -> (x, Def y z))
  [ ("+", Val.FAdd, 0), ("-", Val.FSub, 0), ("*", Val.FMul, 0), ("/", Val.FDiv, 0)
  , ("<", Val.FLt, 0), ("=", Val.FEq, 0), (">", Val.FGt, 0)
  , ("i/",Val.FDivi, 0), ("%", Val.FMod, 0), ("P", Val.FPow, 0)
  , ("G", Val.FMax, 0), ("L", Val.FMin, 0)
  , ("&", Val.FAnd, 0), ("\\",Val.FOr, 0), ("~", Val.FNot, 0)
  , ("'", Val.FCat, 0), ("\"",Val.FCons, 0)
  , ("E", Val.FReshape, 0), ("s#",Val.FShape, 0)
  , ("e@", Val.FPick, 0), ("@",Val.FSelect, 0)
  , ("!", Val.FDrop, 0), (".", Val.FDup, 0), (",", Val.FSwap, 0), (";", Val.FRot, 0)
  , (":", Val.FOver, 0), ("`", Val.FShow, 0), ("^", Val.FCall, 0)
  , ("c<",Val.FAsChars, 0), ("n<", Val.FAsNums, 0), ("i<", Val.FAsInts, 0), ("e<", Val.FAsElems, 0)
  , ("b", Val.FBoth, 1), ("i", Val.FIf, 2), ("d", Val.FDip, 1), ("k", Val.FKeep, 1)
  , ("w", Val.FWhile, 2), ("t", Val.FTimes, 1), ("m", Val.FMap, 1), ("z", Val.FZip, 1)
  , ("c", Val.FCells, 1), ("bc", Val.FBicells, 1), ("s", Val.FRank, 1), ("bs", Val.FBirank, 1)
  ]

_stacks  :: Traversal' RtState (HM.HashMap Ident [Val])
_defs    :: Traversal' RtState (HM.HashMap Ident Def)
_sources :: Traversal' RtState (HM.HashMap FilePath T.Text)
_stacks  f r = f (stacks  r) <&> \x -> r {stacks = x}
_defs    f r = f (defs    r) <&> \x -> r {defs   = x}
_sources f r = f (sources r) <&> \x -> r {sources= x}


type RtM = S.StateT RtState IO

instance CashMonad RtM where
  cashLog (Output x) = liftIO (putStr (T.unpack x))
  cashLog (OutputRed x) = liftIO (putStr ("\x1b[31m" <> T.unpack x <> "\x1b[0m"))
  cashError err = (showErr err >>= cashLog) >> liftIO exitFailure
  effect = liftIO . doEffect
  source name = use (_sources.at name)
  callQuot = call

showErrSrcd :: CashMonad m => RtErr -> m T.Text
showErrSrcd (WithOffset (Position name offset) err) =
  (<>) . \case
    Just src -> formatLine src name offset
    Nothing  -> "at file "<>T.pack (show name)<>" (unavailable)\n"
  <$> source name
  <*> showErrSrcd err
showErrSrcd err = pure (T.pack (show err) <> "\n")



data RtErr
  = CmdNotFound Ident
  | EmptyStream
  | PatNotFound Ident
  | UnexpectedQuot
  | VarNotThere Ident
  | UnfCombinator Fun [[Act]]
  | WithOffset Position RtErr
  | MisshapenQuot [Int]
  deriving (Eq, Show)

instance Error RtErr where
  showErr err = Output <$> showErrSrcd err
  errAsVal = undefined

placeholderActsToVal :: [Act] -> Val
placeholderActsToVal = Quot . (>>= conv)
  where conv :: Act -> [Elem]
        conv (Comb c a) = (asElem . placeholderActsToVal <$> a) <> [ECmd (Comb c [])]
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

addSource :: FilePath -> T.Text -> RtM ()
addSource path src = _sources %= HM.insert path src

run :: [Tok] -> [Val] -> RtM [Val]
run [] s = return s
run os s = use _defs >>= \d-> case cutAct d os of
  Left err         -> cashError err
  Right (act, os') -> doAct act s >>= run os'


runWith :: RtState -> [Tok] -> [Val] -> IO ([Val], RtState)
runWith r os s = S.runStateT (run os s) r


cutQuot :: HM.HashMap Ident Def -> [Tok] -> Either RtErr ([Act], [Tok])
cutQuot defs (Tok loc (QuotF   a) : os) = first (WithOffset loc) ((,os) <$> readQuot defs a)
-- todo do something different
cutQuot defs (Tok loc (QuotUnf a) : os) = first (WithOffset loc) ((,os) <$> readQuot defs a)
cutQuot defs a                          = first singleton <$> cutAct defs a

cutAct' :: HM.HashMap Ident Def -> Obj -> [Tok] -> Either RtErr (Act, [Tok])
cutAct' defs (Cmd ident) os 
  | T.last ident == '^' && T.length ident > 1 =
    case HM.lookup (T.init ident) defs of
      Just (Def call _rity) -> Right (Comb call [], os)
      Nothing               -> Left (CmdNotFound ident)
  | otherwise =
    case HM.lookup ident defs of
      Just (Def call arity) -> readQuotN defs ([], os) arity <&> first (Comb call)
      Nothing               -> Left (CmdNotFound ident)
cutAct' _efs (Numlit i) os =
  (Right . (,os) . Const) case assertInt i of
    Just i' -> Ints (Atom i')
    Nothing -> Nums (Atom i)
cutAct' _efs (Numlits is) os = 
  (Right . (,os) . Const) case traverse assertInt is of
    Just is' -> Ints (listl is')
    Nothing  -> Nums (listl is)
cutAct' _efs (LitLabel l) os = Right (Const (Symbols (Atom (Val.Symbol l))), os)
cutAct' defs (QuotF a) os = (,os) . Const . placeholderActsToVal <$> readQuot defs a
cutAct' defs (QuotUnf a) os = cutAct' defs (QuotF a) os
cutAct' _efs (Literal i t) os | T.null i  = Right (Const (list (T.unpack t)), os)
                              | otherwise = Left (PatNotFound i)
cutAct' _efs (OPush i) os = Right (Push i, os)
cutAct' _efs (OPeek i) os = Right (Peek i, os)
cutAct' _efs (OPop  i) os = Right (Pop  i, os)

cutAct :: HM.HashMap Ident Def -> [Tok] -> Either RtErr (Act, [Tok])
cutAct defs (Tok loc obj : os) = first (WithOffset loc) (cutAct' defs obj os)
cutAct _efs [] = Left EmptyStream

readQuot :: HM.HashMap Ident Def -> [Tok] -> Either RtErr [Act]
readQuot _    [] = Right []
readQuot defs a  = cutAct defs a >>= \(c, xs) -> (c:) <$> readQuot defs xs

readQuotN :: HM.HashMap Ident Def -> ([[Act]], [Tok]) -> Int -> Either RtErr ([[Act]], [Tok])
readQuotN _    (cs, os) 0 = Right (cs, os)
readQuotN defs (cs, os) k = cutQuot defs os >>= \(c, os')-> readQuotN defs (c:cs, os') (k-1)

call :: [Elem] -> [Val] -> RtM [Val]
call os xs = foldM (flip doElem) xs os

doElem :: Elem -> [Val] -> RtM [Val]
doElem (ECmd a) xs = doAct a xs
doElem a xs = pure (unwrap a : xs)
