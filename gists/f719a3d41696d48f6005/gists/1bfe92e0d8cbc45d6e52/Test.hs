{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Main where

import Conduit.Simple
import Control.Applicative
import Control.Concurrent
import Control.Concurrent.Async.Lifted
import Control.Concurrent.Lifted
import Control.Concurrent.STM
import Control.Concurrent.STM.TBMQueue
import Control.Concurrent.STM.TMQueue
import Control.Monad
import Control.Monad.Base
import Control.Monad.Trans
import Control.Monad.Trans.Control
import Control.Monad.Trans.Either
import Data.Bifunctor
import Data.ByteString (ByteString)
import Data.Functor

sinkTBMQueue :: (MonadBaseControl IO m)
             => Int
             -> Sink a m (TBMQueue a)
sinkTBMQueue cap source = do
    q <- liftBase $ newTBMQueueIO cap
    a <- async $ sinkQueue q
    link a
    return q
  where
    sinkQueue q = do
        sink q f source
        liftBase . atomically $ closeTBMQueue q
    f q elem =
        liftBase . atomically $ q <$ writeTBMQueue q elem

sinkTMQueue :: (MonadBaseControl IO m)
            => Sink a m (TMQueue a)
sinkTMQueue source = do
    q <- liftBase newTMQueueIO
    a <- async $ sinkQueue q
    link a
    return q
  where
    sinkQueue q = do
        sink q f source
        liftBase . atomically $ closeTMQueue q
    f q elem =
        liftBase . atomically $ q <$ writeTMQueue q elem

-- "clone" can be arbitrary m so we can't live in STM here
fanoutTMQueue :: (MonadBaseControl IO m)
              => TMQueue a
              -> (a -> m a)
              -> m (TMQueue a, TMQueue a)
fanoutTMQueue q clone = do
    res <- liftBase $ (,) <$> newTMQueueIO <*> newTMQueueIO
    a <- async $ uncurry fanout res
    link a
    return res
  where
    fanout q1 q2 = liftBase (atomically (readTMQueue q)) >>= \case
        Just x1 -> clone x1 >>= \x2 -> do
            _ <- liftBase $
                 atomically (writeTMQueue q1 x1) `concurrently`
                 atomically (writeTMQueue q2 x2)
            fanout q1 q2
        Nothing -> liftBase $
            atomically (closeTMQueue q1) `concurrently`
            atomically (closeTMQueue q2)

cloneSource :: (MonadBaseControl IO m)
            => Source m a -> (a -> m a) -> m (Source m a, Source m a)
cloneSource src clone = do
    q <- sinkTMQueue src
    join bimap sourceQueue <$> fanoutTMQueue q clone
  where
    sourceQueue q = source (go q)
    go q z yield = liftBase (atomically (readTMQueue q)) >>= \case
        Just x -> do
            next <- yield z x
            go q next yield
        Nothing -> return z

sauce = sourceFile "Test.hs" :: Source IO ByteString
sink1 = sinkFile "out1"
sink2 = sinkFile "out2"

main :: IO ()
main = do
  (s1, s2) <- cloneSource sauce return
  sink1 s1
  sink2 s2
