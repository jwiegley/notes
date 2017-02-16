{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module Froo where

import Control.Applicative
import Test.QuickCheck

data Free f a = Pure a | Free (f (Free f a)) deriving Functor

instance (Applicative f, Eq a, Eq (f (Free f a))) => Eq (Free f a) where
    Pure x == Pure y = x == y
    Pure _ == Free _ = False
    Free _ == Pure _ = False
    Free x == Free y = x == y

data Froo f a = L a | B (Froo f (f a)) deriving Functor

instance Applicative f => Applicative (Froo f) where
    pure = L
    L f <*> L x = L (f x)
    B f <*> L x = B (fmap (fmap ($ x)) f)
    L f <*> B x = B (fmap (fmap f) x)
    B f <*> B x = B (liftA2 (<*>) f x)

instance (Applicative f, Eq a, Eq (f a)) => Eq (Froo f a) where
    L x == L y = x == y
    L _ == B _ = False
    B _ == L _ = False
    B x == B y = case liftA2 (==) x y of
        L b -> b
        _ -> False

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

from :: (Traversable f, Applicative f) => Free f a -> Froo f a
from (Pure x) = L x
from (Free n) = B (sequenceA (fmap from n))

data Pair a = Pair a a deriving (Eq, Functor)

instance Show a => Show (Pair a) where
    show (Pair x y) = "Pair (" ++ show x ++ ") (" ++ show y ++ ")"

instance Applicative Pair where
    pure x = Pair x x
    Pair f g <*> Pair x y = Pair (f x) (g y)

instance Foldable Pair where
  foldMap f (Pair x y) = f x `mappend` f y

instance Traversable Pair where
    traverse f (Pair x y) = Pair <$> f x <*> f y

instance Arbitrary a => Arbitrary (Pair a) where
    arbitrary = Pair <$> arbitrary <*> arbitrary

instance Show (Froo Pair Int) where
    show x = show (to x)

instance Arbitrary a => Arbitrary (Froo Pair a) where
    arbitrary = do
        b <- arbitrary
        if b
            then L <$> arbitrary
            else B <$> arbitrary

instance Arbitrary a => Arbitrary (Free Pair a) where
    arbitrary = do
        b <- arbitrary
        if b
            then Pure <$> arbitrary
            else Free <$> arbitrary

-- Every Free *cannot* be embedded in Froo
prop_from_to :: Free Pair Int -> Bool
prop_from_to x = to (from x) == x

-- Every Froo can be embedded in Free
prop_to_from :: Froo Pair Int -> Bool
prop_to_from x = from (to x) == x

-- For trees of regular structure, Free and Froo are equivalent. But Free
-- allows irregular structures. For example:
--
-- Regular:
--
--         o
--       /   \
--      o     o
--     / \   / \
--    o   o o   o
--
-- Irregular:
--
--         o
--       /   \
--      o     o
--     / \
--    o   o

test1 :: Froo Pair Int
test1 = B (B (L (Pair (Pair 3 12) (Pair 2 5))))

test2 :: Free Pair Int
test2 = Free (Pair (Free (Pair (Pure 3) (Pure 12)))
                   (Free (Pair (Pure 2) (Pure  5))))

test3 :: Bool
test3 = test1 == from test2

test4 :: Bool
test4 = to test1 == test2
