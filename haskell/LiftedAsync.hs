module LiftedAsync where

import Control.Concurrent.Async.Lifted
import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Control.Monad

main :: IO ()
main = void $ flip runStateT 0 $ do
    x <- async (modify (+2)) `race` async (modify (+5))
    _ <- wait (either id id x)
    s <- get
    liftIO $ putStrLn $ "State now is: " ++ show s
