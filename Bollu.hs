{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Bollu where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.Cont
import Data.Maybe
import Data.Monoid
import Debug.Trace

from :: (a -> b) -> a -> Cont r b
from f x = return (f x)

to :: (forall r. a -> Cont r b) -> a -> b
to f x = runCont (f x) id

escapeGreater10 :: Int -> Cont Int Int
escapeGreater10 num = trace "1..\n" $ do
    x <- trace "2..\n" $ callCC $ \k ->
        if num >= 10
        then do
             trace "3..\n" $ k 0
        else do
             trace "4..\n" $ return (num + 1)
    trace "5..\n" $ return x

main = do
    let nums = fmap (\n -> runCont (escapeGreater10 n) id) [0..12]
    print nums
