{-# LANGUAGE DeriveFunctor #-}

module Broken where

import Test.QuickCheck

data Broken a = Broken a deriving Functor

instance Foldable Broken where
    foldr f z (Broken x) = f x (f x (f x z))

prop_broken :: (Int -> Int -> Int) -> (Int -> Int) -> Int -> Broken Int -> Bool
prop_broken f g z xs =
    foldr f z (fmap g xs) == foldr (f . g) z xs
