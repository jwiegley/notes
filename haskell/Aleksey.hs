{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Aleksey where

import Control.Applicative
import Control.Monad

newtype Yoneda f a = Y (forall b. (a -> b) -> f b)

instance Functor (Yoneda f) where fmap f (Y m) = Y (\k -> m (k . f))

data Coyoneda f a = forall b. C (b -> a, f b)

instance Functor (Coyoneda f) where fmap f (C (g, v)) = C (f . g, v)

data Free f a where
    Pure :: a -> Free f a
    Free :: Coyoneda f (Free f a) -> Free f a

data Free' f a where
    Pure' :: a -> Free' f a
    Free' :: Yoneda f (Free' f a) -> Free' f a

retract :: Monad f => Free' f a -> f a
retract (Pure' a) = return a
retract (Free' (Y as)) = as id >>= retract
