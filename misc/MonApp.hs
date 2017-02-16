{-# LANGUAGE OverloadedStrings #-}

module MonApp where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

(<*>) :: (Functor f, Monad f) => f (a -> b) -> f a -> f b
f <*> x = f >>= flip fmap x

main :: IO ()
main = undefined
