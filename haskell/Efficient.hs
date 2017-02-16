{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}

module Efficient where

import Data.List
import Data.Constraint
import Data.Typeable

data Foo a = Foo a
newtype AtoB = AtoB (forall t. Foo t -> Foo t)

scramble :: Eq a => [a] -> [[a]]
scramble [] = []
scramble (x:xs) = (x : is) : scramble isnt
  where (is, isnt) = partition (==x) xs

type family ConstraintOf a :: * -> Constraint where
    ConstraintOf Int = Ord

foo :: (forall c. Typeable c => c) -> TypeRep
foo k = k (10 :: Int)
