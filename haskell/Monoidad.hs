{-# LANGUAGE OverloadedStrings #-}

module Monoidad where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

data Monoidad m a = Monoidad m a

instance Functor (Monoidad m) where
    fmap f (Monoidad m a) = Monoidad m (f a)

instance Monoid m => Monad (Monoidad m) where
    return = Monoidad mempty
    Monoidad m a >>= f =
        let Monoidad m' a' = f a
        in Monoidad (m <> m') a'

main :: IO ()
main = undefined
