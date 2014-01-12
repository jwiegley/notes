{-# LANGUAGE OverloadedStrings #-}

module Prog1 where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

prog1 :: IO a -> (a -> IO b) -> IO a
prog1 m body = do
    x <- m
    _ <- body x
    return x

main :: IO ()
main = do
    x <- prog1 (return 10) $ \_ -> do
        return 20
    print x
