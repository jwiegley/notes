{-# LANGUAGE OverloadedStrings #-}

module VectorTest where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Vector.Unboxed.Mutable as VM

main :: IO ()
main = do
    v <- VM.new 1024 :: IO (VM.IOVector Int)
    s <- foldM (\i x -> (+) <$> pure i <*> VM.read v x) 0 [0..1023]
    print s
