{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Feuer where

import Data.Functor.Contravariant
import Data.Semigroup
import GHC.Exts (Constraint)

-- A Contravariant Functor in x, but Invariant in y
data Feuer x y where
    -- Defines the imagine of x in y, and some binary operation on y
    Feuer :: Semigroup y => (x -> y) -> Feuer x y

newtype FeuerFlip y x = FeuerFlip { getFeuerFlip :: Feuer x y }

instance Contravariant (FeuerFlip y)

class Functor f => RFunctor f where
    type C f :: * -> Constraint
    rfmap :: C f y => (x -> y) -> f x -> f y

instance Functor (Feuer x)
instance RFunctor (Feuer x) where
    type C (Feuer x) = Semigroup

-- Must be a homorphism
transform :: Semigroup y' => (x' -> x) -> (y -> y') -> Feuer x y -> Feuer x' y'
transform f g x = rfmap g (getFeuerFlip (contramap f (FeuerFlip x)))
