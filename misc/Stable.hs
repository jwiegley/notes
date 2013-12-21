{-# LANGUAGE OverloadedStrings #-}

module Stable where

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Foreign.StablePtr

data Foo = Foo (StablePtr (TVar Int))

test :: Foo -> IO ()
test (Foo ptr) = do
    tv <- deRefStablePtr ptr
    atomically $ modifyTVar tv (+1)

main :: IO ()
main = do
    tv <- newTVarIO 0
    sp <- newStablePtr tv
    let f = Foo sp
    test f
    test f
    test f
    tv' <- deRefStablePtr sp
    x <- readTVarIO tv'
    print x
