{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Data.Monoid

-- When f is a Functor, DMonoid f is isomorphic to f.
data DMonoid a = DMonoid (a -> a)

instance Monoid f => Monoid (DMonoid f) where
    mempty = DMonoid id
    DMonoid g `mappend` DMonoid k = DMonoid $ g <> k

lowerDMonoid :: Monoid a => DMonoid a -> a
lowerDMonoid (DMonoid k) = k mempty

liftDMonoid :: Monoid a => a -> DMonoid a
liftDMonoid a = DMonoid $ \k -> mappend k a

main :: IO ()
main = undefined
