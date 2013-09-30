{-# LANGUAGE PolymorphicComponents, RankNTypes, TypeFamilies #-}

module Traversal where

import Control.Comonad
import Control.Comonad.Identity
import Data.Functor

newtype Context c d b = Context {
  runContext :: forall f. Functor f => (c -> f d) -> b
}

instance c ~ d => Comonad (Context c d) where
  extract (Context f) = runIdentity (f Identity)