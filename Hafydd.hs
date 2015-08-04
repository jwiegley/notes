{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Hafydd where

import Control.Monad.Free.Church

import Data.Foldable
import Data.Traversable

data PropF r
  = PTrue
  | PFalse
  | PAnd r r
  | POr  r r
  | PNot r
  deriving (Show, Functor, Foldable, Traversable)

type Prop = F PropF

sign s x = fromIntegral (x * s)

class Misty m where
  banana :: (a -> m b) -> m a -> m b
  unicorn :: a -> m a
  -- Exercise 6
  -- Relative Difficulty: 3
  -- (use banana and/or unicorn)
  furry' :: (a -> b) -> m a -> m b
  furry' = \f -> banana (unicorn . f)
