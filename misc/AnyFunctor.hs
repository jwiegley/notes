{-# LANGUAGE OverloadedStrings #-}

module AnyFunctor where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

data AnyFunctor a b = AnyFunctor a (a -> b)

instance Functor (AnyFunctor a) where
    fmap f (AnyFunctor x g) = AnyFunctor x (f .g)

functorize :: a -> (a -> b) -> AnyFunctor a b
functorize = AnyFunctor

main :: IO ()
main = undefined
