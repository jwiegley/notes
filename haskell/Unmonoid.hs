{-# LANGUAGE DefaultSignatures #-}

module Unmonoid where

-- | An Unmonoid is a monoid that is essentially reversible, obeying these laws:
--
--   null (unappend mempty)
--   (x, mempty) `elem` unappend x
--   (mempty, x) `elem` unappend x
--   (x, y)      `elem` unappend (x <> y)
--   forall x y, (x, y) `elem` unappend z -> x <> y = z
class Monoid m => Unmonoid m where
  unappend :: m -> ((m, m) -> Bool)
  default unappend :: Eq m => m -> ((m, m) -> Bool)
  unappend m = \(x, y) -> x <> y == m
