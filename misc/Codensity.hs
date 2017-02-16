{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

module Codensity where

import Test.QuickCheck
import Data.Functor.Identity
import Data.Monoid

newtype Codensity m a =
  Codensity { runCodensity :: forall r. (a -> r) -> m r }

to :: Monad m => m a -> Codensity m a
to x = Codensity $ flip fmap x

from :: Monad m => Codensity m a -> m a
from k = runCodensity k id

prop_right = \x -> (from . to) x == (x :: Identity Int)
prop_left  = \x -> (to . from) x == (x :: Codensity Identity Int)

-- to :: Endo [a] -> [a]
-- to xs = appEndo xs []

-- from :: [a] -> Endo [a]
-- from xs = Endo $ (++ xs)

-- -- forall r. (a -> e -> r) -> e -> r

-- instance Eq a => Eq (Endo [a]) where
--   Endo x == Endo y = x [] == y []

-- instance Show a => Show (Endo [a]) where
--   show (Endo x) = show (x [])

-- instance Arbitrary a => Arbitrary (Endo [a]) where
--   arbitrary = from <$> arbitrary

-- prop_right = \x -> (from . to) x == (x :: Endo [Int])
-- prop_left  = \x -> (to . from) x == (x :: [Int])
