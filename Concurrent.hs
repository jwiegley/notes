{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Concurrent where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.Async.Lifted
import Control.Monad
import Control.Monad.Base
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Free
import Data.Functor.Identity

instance (MonadBase b m, Functor f) => MonadBase b (FreeT f m) where
    liftBase = liftBaseDefault

instance (MonadBaseControl b m, Functor f)
         => MonadBaseControl b (FreeT f m) where
    newtype StM (FreeT f m) a =
        StMFreeT { unStMFreeT :: StM m (FreeF f a (FreeT f m a)) }
    liftBaseWith f =
        FreeT $ liftM Pure $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMFreeT $ runInBase $ runFreeT k
    restoreM (StMFreeT m) = FreeT . restoreM $ m

newtype ConcurrentT m a = ConcurrentT { runConcurrentT :: FreeT Identity m a }

concurrent :: Monad m => ConcurrentT m a -> m a
concurrent = iterT runIdentity . runConcurrentT

instance MonadTrans ConcurrentT where
    lift = ConcurrentT . lift

instance MonadIO m => MonadIO (ConcurrentT m) where
    liftIO = ConcurrentT . liftIO

instance Monad m => Functor (ConcurrentT m) where
    fmap f (ConcurrentT m) = ConcurrentT (fmap f m)

instance Monad m => Monad (ConcurrentT m) where
    return = ConcurrentT . FreeT . return . Pure
    ConcurrentT (FreeT m) >>= k = ConcurrentT . FreeT $ do
        a <- m -- serialize actions in the Monad
        case a of
            Pure a' -> runFreeT . runConcurrentT $ k a'
            Free r  -> return . Free $ fmap (>>= runConcurrentT . k) r

instance MonadBaseControl IO m => Applicative (ConcurrentT m) where
    pure = return
    ConcurrentT f <*> ConcurrentT a =
        -- run actions concurrently in the Applicative
        ConcurrentT $ do
            (f', a') <- concurrently f a
            return $ f' a'

main :: IO ()
main = do
    putStrLn "Using the Monad instance, things happen serially"
    concurrent $ do
        delay "start 1" (return ()) "end 1"
        delay "start 2" (return ()) "end 2"

    putStrLn "Using the Applicative instance, things happen concurrently"
    print =<<
        concurrent
            ((+) <$> delay "scompute 1" (lift $ return (1 :: Int)) "ecompute 1"
                 <*> delay "scompute 2" (return (2 :: Int)) "ecompute 2")
  where
    delay :: String -> ConcurrentT IO a -> String -> ConcurrentT IO a
    delay before f after = do
        liftIO $ putStrLn before
        liftIO $ threadDelay 2000000
        x <- f
        liftIO $ putStrLn after
        return x
