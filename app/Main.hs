module Main where
import Parse (parse)
import qualified Data.Text.IO
import Rt (defaultRtState, RtM, run)
import System.IO (stdout, hFlush)
import Val (Val)
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Control.Monad.Trans.State as S
import Arr (shortShow)



infixr 8 .:
(.:) :: (c->d) -> (a->b->c) -> a->b->d
(f .: g) x y = f (g x y)

main :: IO ()
main = S.evalStateT (bee []) defaultRtState

bee :: [Val] -> RtM ()
bee o = liftIO ( putStr ("\x1b[32m" <> (reverse o >>= (' ':).shortShow) <> " \x1b[0m")
              >> hFlush stdout
              >> Data.Text.IO.getLine)
        >>= liftIO . parse 
        >>= flip run o
        >>= bee