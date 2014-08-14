{-# LANGUAGE BangPatterns #-}

module Strict where

import Control.Applicative
import Control.Monad

newtype Strict a = Strict { getStrict :: a }
  deriving Show

instance Functor Strict where
    fmap f (Strict !x) = Strict $! f x

instance Applicative Strict where
    pure = return
    (<*>) = ap

instance Monad Strict where
    return !x = Strict x
    (Strict !x) >>= f =
        let Strict !y = f x
        in Strict y
