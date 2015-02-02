{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Data.Conduit.Concurrent where

import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Monad (forM_)
import Control.Monad.IO.Class
import Control.Monad.Trans.Control
import Data.Conduit
import Data.Conduit.List
import Prelude hiding (mapM_)

import Control.Concurrent (threadDelay)

buffer :: (MonadBaseControl IO m, MonadIO m)
       => Int -> Producer m a -> Consumer a m b -> m b
buffer size input output = do
    chan <- liftIO $ newTBQueueIO size
    control $ \runInIO ->
        withAsync (runInIO $ input $$ mapM_ (send chan)) $ \input' ->
            withAsync (runInIO $ recv chan $$ output) $ \output' -> do
                link2 input' output'
                wait output'
  where
    send chan = liftIO . atomically . writeTBQueue chan . Just

    recv chan = do
        mx <- liftIO $ atomically $ readTBQueue chan
        case mx of
            Nothing -> return ()
            Just x  -> yield x >> recv chan

($$&) :: (MonadIO m, MonadBaseControl IO m)
      => Producer m a -> Consumer a m b -> m b
($$&) = buffer 64

main :: IO ()
main = do
    liftIO $ putStrLn "Sequential case..."
    producer $$ consumer
    liftIO $ putStrLn "Concurrent case..."
    producer $$& consumer
    liftIO $ putStrLn "Infinite producer..."
    infiniteProducer $$& consumer
    liftIO $ putStrLn "Exceptional producer..."
    error "BOO!" $$& consumer
  where
    producer = do
        liftIO $ putStrLn "Producing..."
        yield (1 :: Int)
        liftIO $ putStrLn "Producing..."
        yield 2
        liftIO $ putStrLn "Producing..."
        yield 3
        liftIO $ putStrLn "Done producing"

    infiniteProducer = forM_ [1..] $ \i -> do
        liftIO $ putStrLn $ "Producing " ++ show i
        yield (i :: Int)

    consumer = do
        liftIO $ putStrLn "Consuming..."
        liftIO . print =<< await
        liftIO $ threadDelay 1000000
        liftIO $ putStrLn "Consuming..."
        liftIO . print =<< await
        liftIO $ threadDelay 1000000
        liftIO $ putStrLn "Consuming..."
        liftIO . print =<< await
        liftIO $ putStrLn "Done consuming"
