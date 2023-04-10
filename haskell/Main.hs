module Main
( main
) where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad

-- -------------------------------------------------------------------------- --
-- Producer

-- | Given an action, the producer repeatedly runs the action to produce times
-- that it hands of to the consumer.
--
producer :: TQueue a -> IO a -> IO ()
producer queue a = forever $ a >>= \x ->
    atomically $ do
      writeTQueue queue $! x

-- -------------------------------------------------------------------------- --
-- Consumer

-- | Given an action, the consumer receives itmes from the producer and
-- applies the action to each item.

consumer :: TQueue a -> (a -> IO ()) -> IO ()
consumer queue a = forever $ a =<< do
    atomically $ do
        x <- readTQueue queue
        return $! x

-- -------------------------------------------------------------------------- --
-- Main

main :: IO ()
main = do
    queue <- newTQueueIO
    void $ forkIO $ producer queue $ do
        return 1
    void $ forkIO $ consumer queue $ \a -> do
        threadDelay 1
        print a
    forever $ threadDelay 1000

