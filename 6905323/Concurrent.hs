{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Concurrent where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.Async.Lifted
import Control.Concurrent.STM
import Control.Exception.Lifted
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Free
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import Data.Tagged
import Data.Time
import Data.Traversable

instance (MonadBase b m, Functor f) => MonadBase b (FreeT f m) where
    liftBase = liftBaseDefault

instance (MonadBaseControl b m, Functor f)
         => MonadBaseControl b (FreeT f m) where
    newtype StM (FreeT f m) a = StMFreeT (StM m (FreeF f a (FreeT f m a)))
    liftBaseWith f =
        FreeT $ liftM Pure $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMFreeT $ runInBase $ runFreeT k
    restoreM (StMFreeT m) = FreeT . restoreM $ m

newtype ConcurrentT m a = ConcurrentT { getConcurrentT :: FreeT Identity m a }

runConcurrentT :: Monad m => ConcurrentT m a -> m a
runConcurrentT (ConcurrentT m) = iterT runIdentity m

instance Monad m => Functor (ConcurrentT m) where
    fmap f (ConcurrentT m) = ConcurrentT (fmap f m)

instance Monad m => Monad (ConcurrentT m) where
    return = ConcurrentT . FreeT . return . Pure
    ConcurrentT (FreeT m) >>= k = ConcurrentT . FreeT $ do
        a <- m -- serialize actions in the Monad
        case a of
            Pure a' -> runFreeT . getConcurrentT $ k a'
            Free r  -> return . Free $ fmap (>>= getConcurrentT . k) r

instance MonadBaseControl IO m => Applicative (ConcurrentT m) where
    pure = return
    ConcurrentT f <*> ConcurrentT a =
        -- run actions concurrently in the Applicative
        ConcurrentT $ withAsync a $ \a' -> ($) <$> f <*> wait a'

instance MonadTrans ConcurrentT where
    lift = ConcurrentT . lift

instance MonadIO m => MonadIO (ConcurrentT m) where
    liftIO = ConcurrentT . liftIO

instance (MonadBaseControl IO m, MonadBase IO m)
         => MonadBase IO (ConcurrentT m) where
    liftBase = liftBaseDefault

instance MonadBaseControl IO m => MonadBaseControl IO (ConcurrentT m) where
    newtype StM (ConcurrentT m) a = StMConcurrentT (StM (FreeT Identity m) a)
    liftBaseWith f =
        ConcurrentT $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMConcurrentT $ runInBase $ getConcurrentT k
    restoreM (StMConcurrentT m) = ConcurrentT . restoreM $ m

newtype ConcurrentPoolT s m a = ConcurrentPoolT
    { getConcurrentPoolT :: ReaderT (TVar (Tagged s Int)) (ConcurrentT m) a }

runConcurrentPoolT :: MonadIO m
                   => Int -> (forall s. ConcurrentPoolT s m a) -> m a
runConcurrentPoolT count (ConcurrentPoolT m) = do
    counter <- liftIO $ newTVarIO (Tagged count)
    runConcurrentT $ runReaderT m counter

instance Monad m => Functor (ConcurrentPoolT s m) where
    fmap f (ConcurrentPoolT m) = ConcurrentPoolT (fmap f m)

instance Monad m => Monad (ConcurrentPoolT s m) where
    return = ConcurrentPoolT . return
    ConcurrentPoolT m >>= k = ConcurrentPoolT $ m >>= getConcurrentPoolT . k

instance (MonadBaseControl IO m, MonadIO m)
         => Applicative (ConcurrentPoolT s m) where
    pure = return
    ConcurrentPoolT f <*> ConcurrentPoolT a = ConcurrentPoolT $ do
        counter <- ask
        run counter a $ \aa -> ($) <$> f <*> wait aa
      where
        run counter g = withAsync $ bracket_
            (modifyCounter counter pred False)
            (modifyCounter counter succ True) g

        modifyCounter counter g doit = liftIO $ atomically $ do
            count <- readTVar counter
            check $ doit || count > 0
            writeTVar counter (g count)

instance MonadTrans (ConcurrentPoolT s) where
    lift = ConcurrentPoolT . lift . lift

instance MonadIO m => MonadIO (ConcurrentPoolT s m) where
    liftIO = ConcurrentPoolT . liftIO

instance (MonadBaseControl IO m, MonadBase IO m, MonadIO m)
         => MonadBase IO (ConcurrentPoolT s m) where
    liftBase = liftBaseDefault

instance (MonadBaseControl IO m, MonadIO m)
         => MonadBaseControl IO (ConcurrentPoolT s m) where
    newtype StM (ConcurrentPoolT s m) a =
        StMConcurrentPoolT
            (StM (ReaderT (TVar (Tagged s Int)) (ConcurrentT m)) a)
    liftBaseWith f =
        ConcurrentPoolT $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMConcurrentPoolT $ runInBase $ getConcurrentPoolT k
    restoreM (StMConcurrentPoolT m) = ConcurrentPoolT . restoreM $ m

main :: IO ()
main = do
    putStrLn "Using the Monad instance, things happen serially"
    start <- getCurrentTime
    runConcurrentT $ do
        delay "start 1" (return ()) "end 1"
        delay "start 2" (return ()) "end 2"
    stop <- getCurrentTime
    print $ diffUTCTime stop start

    putStrLn "Using the Applicative instance, things happen concurrently"
    start' <- getCurrentTime
    print =<<
        runConcurrentT
            (sequenceA
                [ delay "scompute 1" (return (1 :: Int)) "ecompute 1"
                , delay "scompute 2" (return (2 :: Int)) "ecompute 2"
                , delay "scompute 3" (return (3 :: Int)) "ecompute 3"
                , delay "scompute 4" (return (4 :: Int)) "ecompute 4"
                , delay "scompute 5" (return (5 :: Int)) "ecompute 5"
                , delay "scompute 6" (return (6 :: Int)) "ecompute 6"
                , delay "scompute 7" (return (7 :: Int)) "ecompute 7"
                , delay "scompute 8" (return (8 :: Int)) "ecompute 8"
                , delay "scompute 9" (return (9 :: Int)) "ecompute 9"
                , delay "scompute 10" (return (10 :: Int)) "ecompute 10"
                ])
    stop' <- getCurrentTime
    print $ diffUTCTime stop' start'

    putStrLn "Using a pool restricts the number of concurrent computations"
    start'' <- getCurrentTime
    print =<<
        runConcurrentPoolT 5
            (sequenceA
                [ delay "scompute 1" (return (1 :: Int)) "ecompute 1"
                , delay "scompute 2" (return (2 :: Int)) "ecompute 2"
                , delay "scompute 3" (return (3 :: Int)) "ecompute 3"
                , delay "scompute 4" (return (4 :: Int)) "ecompute 4"
                , delay "scompute 5" (return (5 :: Int)) "ecompute 5"
                , delay "scompute 6" (return (6 :: Int)) "ecompute 6"
                , delay "scompute 7" (return (7 :: Int)) "ecompute 7"
                , delay "scompute 8" (return (8 :: Int)) "ecompute 8"
                , delay "scompute 9" (return (9 :: Int)) "ecompute 9"
                , delay "scompute 10" (return (10 :: Int)) "ecompute 10"
                ])
    stop'' <- getCurrentTime
    print $ diffUTCTime stop'' start''
  where
    delay :: MonadIO m => String -> m a -> String -> m a
    delay before f after = do
        liftIO $ putStrLn before
        liftIO $ threadDelay 2000000
        x <- f
        liftIO $ putStrLn after
        return x
