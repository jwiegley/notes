{-# LANGUAGE RankNTypes #-}

module Impred where

class RandomGen g where

data Context a = Context a

foo :: Context (forall g. RandomGen g => g)
foo = undefined
