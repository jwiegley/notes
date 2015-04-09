{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Unlift where

import Control.Monad
import Control.Concurrent.Async
import Control.Monad.Trans.Control

concurrentlyG' :: forall m a b. MonadBaseControl IO m
               => m a -> m b -> m (a, b)
concurrentlyG' f g = control $ \run ->
    go run =<< concurrently (run f) (run g)
  where
    go :: (forall x. m x -> IO (StM m x))
       -> (StM m a, StM m b)
       -> IO (StM m (a, b))
    go run (x, y) = run $ liftM2 (,) (restoreM x :: m a) (restoreM y :: m b)
