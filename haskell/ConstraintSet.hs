{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module ConstraintSet where

import Data.Set

data Foo a where
    Foo :: Eq a => a -> Foo a

instance Functor Foo where
    fmap f (Foo x) = Foo (f x)
