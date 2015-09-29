{-# LANGUAGE RankNTypes #-}

module Codensity where

to :: Monad m => m a -> (a -> m r) -> m r
to x f = x >>= f

from :: Monad m => (forall r. (a -> m r) -> m r) -> m a
from k = k return
