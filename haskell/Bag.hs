{-# LANGUAGE RankNTypes #-}

module Bag where

import Data.Set

newtype Bag a = Bag { openBag :: Eq a => (Set a, a -> Int) }

denote :: Eq a => [a] -> Bag a
denote [] = Bag (const 0)
denote (x:xs) = Bag (\y -> (if x == y then 1 else 0) + openBag (denote xs) y)

-- denote (fmap f b) = fmap f (denote b)

-- denote (fmap f []) = fmap f (denote [])
-- denote (map f []) = fmap f (Bag (const 0))
-- denote [] = fmap f (Bag (const 0))
-- Bag (const 0) = fmap f (Bag (const 0))

instance Functor Bag where
    fmap f (Bag g) = Bag (\b -> _)
