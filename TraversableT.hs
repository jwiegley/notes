{-# LANGUAGE RankNTypes #-}

module TraversableT where

import Control.Applicative
import Control.Monad hiding (msum)
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Foldable
import Data.Traversable

newtype TraversableT f m a = TraversableT
    { runTraversableT :: (Applicative f, Traversable f) => f (m a) }

instance MonadPlus m => Monad (TraversableT f m) where
  return x = TraversableT $ pure (return x)
  TraversableT m >>= f = TraversableT $ do
       traverse (\x -> x >>= runTraversableT . f) m
