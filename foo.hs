{-# LANGUAGE OverloadedStrings #-}

module Foo where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

class Foo a b | a -> b

foo :: (Foo a b, Foo a c) => a -> b -> c
foo _ x = x

main :: IO ()
main = foo 10 20
