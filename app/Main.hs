module Main where
import Parse (parse)
import qualified Data.Text.IO
import Rt (defaultRtState, RtM, run, addSource)
import System.IO (stdout, hFlush)
import Val (Val, shortShow)
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Control.Monad.Trans.State as S



infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

main :: IO ()
main = S.evalStateT (repl 1 []) defaultRtState

repl :: Int -> [Val] -> RtM ()
repl n o = do 
  src <- liftIO ( putStr ("\x1b[32m" <> (reverse o >>= (' ':).shortShow) <> " \x1b[0m")
                >> hFlush stdout
                >> Data.Text.IO.getLine)
  toks <- liftIO (parse name src)
  addSource name src
  run toks o
    >>= repl (n+1)
  where name = "[repl "<>show n<>"]"