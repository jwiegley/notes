module Main where

import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.Logic
import Control.Monad.Trans.Class
import Control.Monad.Trans.State

main :: IO ()
main = do
    print $ flip runStateT 0 $ do
        x <- lift [1,2,3]
        liftIO $ putStrLn x
        id += (1 :: Int)
