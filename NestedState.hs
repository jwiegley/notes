{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module NestedState where

import Control.Monad.State.Class as C
import Control.Monad.Trans.State as T

instance MonadState b m => MonadState (a, b) (StateT a m) where
    get = do
        x <- T.get
        y <- C.get
        return (x, y)

instance MonadState a m => MonadState (a, b) (StateT b m) where
    get = do
        x <- T.get
        y <- C.get
        return (x, y)
