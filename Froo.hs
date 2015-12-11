{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Froo where

import Control.Applicative

data Froo f a = L a | B (Froo f (f a)) deriving Functor
data Free f a = Pure a | Free (f (Free f a)) deriving Functor

instance Applicative f => Applicative (Froo f) where
    pure = L
    L f <*> L x = L (f x)
    B f <*> L x = B (fmap (fmap ($ x)) f)
    L f <*> B x = B (fmap (fmap f) x)
    B f <*> B x = B (liftA2 (<*>) f x)

instance (Show a, Show (f (Free f a))) => Show (Free f a) where
    show (Pure x) = "Pure " ++ show x
    show (Free x) = "Free (" ++ show x ++ ")"

to :: Functor f => Froo f a -> Free f a
to (L x) = Pure x
to (B x) = wrap (to x)
  where
    wrap :: Functor f => Free f (f a) -> Free f a
    wrap (Pure y) = Free (fmap Pure y)
    wrap (Free y) = Free (fmap wrap y)

from :: (Traversable f, Applicative f, Functor f) => Free f a -> Froo f a
from (Pure x) = L x
from (Free n) = B (sequenceA (fmap from n))
