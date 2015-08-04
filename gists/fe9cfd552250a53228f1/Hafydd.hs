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
