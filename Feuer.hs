{-# LANGUAGE GADTs #-}

module Feuer where

-- A Contravariant Functor in x, but Invariant in y
data Feuer x y where
    -- Defines the imagine of x in y, and some binary operation on y
    Feuer :: (x -> y) -> (y -> y -> y) -> Feuer x y

-- Must be a homorphism
transform :: Feuer x y -> Feuer x' y'
transform = undefined
