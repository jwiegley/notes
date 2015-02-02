{-# LANGUAGE RankNTypes #-}

module Nat where

import Prelude (Show)

data Nat = Z | S Nat deriving Show

data Maybe a = Nothing | Just a

fromNat :: Nat -> Maybe Nat
fromNat Z = Nothing
fromNat (S x) = Just x

toNat :: Maybe Nat -> Nat
toNat Nothing = Z
toNat (Just x) = S x

type Church = forall r. (r -> r) -> r -> r

id :: forall a. a -> a
id x = x

toChurch :: Nat -> Church
toChurch Z = \_ -> \y -> y
toChurch (S n) = \x -> \y -> x ((toChurch n) x y)

zero = \x -> \y -> y
one = \x -> \y -> x y
two = \x -> \y -> x (x y)

succ = \x -> (\a -> \b -> a (x a b))

fromChurch :: Church -> Nat
fromChurch f = f S Z
