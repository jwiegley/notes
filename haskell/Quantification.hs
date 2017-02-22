{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Quantification where

import Data.Void

positive :: forall a. a

negative :: forall a. forall r. a -> r
