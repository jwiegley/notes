module Main where

import Control.Concurrent
import Control.Concurrent.Async.Lifted
import Control.Monad.IO.Class
import Control.Monad.Trans.Control

speculate :: (Monad m, MonadBaseControl IO m, Eq b)
          => (a -> m b) -> (b -> m c) -> a -> (a -> b) -> m c
speculate f g x guess = do
    let w = guess x
    z <- async (g w)
    y <- f x
    if y == w
        then liftIO (wait z)
        else liftIO (cancel z) >> g y

main = do
    print =<< speculate foo bar 1 (const 2)
    print =<< speculate foo bar 1 (const 11)
  where
    foo x = do
        putStrLn $ "in foo(" ++ show x ++ ")..."
        threadDelay 5000000
        return $ x + 10

    bar x = do
        putStrLn $ "in bar(" ++ show x ++ ")..."
        threadDelay 10000000
        return $ x + 33
