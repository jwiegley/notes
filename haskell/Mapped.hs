module Mapped where

import Control.Applicative
import Control.Monad
import Data.Profunctor

data Mapped a b = Mapped a (a -> b)

instance Functor (Mapped a) where
    fmap f (Mapped x g) = Mapped x (f . g)

instance Applicative (Mapped a) where
    pure x = Mapped x id
    Mapped f g <*> Mapped x h = Mapped (g f x) h

instance Monad (Mapped a) where
    return = pure
    -- join (Mapped (Mapped x f) g) = Mapped x (f . g)
    Mapped x g >>= f = f g x
