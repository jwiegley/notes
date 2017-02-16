{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module PList where

import Data.Singletons.Prelude

data List a = Nil | Cons a (List a) deriving Show

data Sorted (l :: List a) where
    SortedNil :: Sorted 'Nil
    SortedSing :: forall a. Sorted ('Cons a 'Nil)
    SortedCons :: forall a b xs. ((a :< b) ~ 'True)
        => Sorted ('Cons b xs) -> Sorted ('Cons a ('Cons b xs))

is_sorted :: forall (xs :: List a). Sorted xs
is_sorted Nil = SortedNil
is_sorted (Cons x Nil) = SortedSing
is_sorted (Cons x (Cons y xs)) = SortedCons (is_sorted xs)

main :: IO ()
main = do
    let xs = Cons 1 (Cons 2 (Cons 3 Nil))
    let sxs = SortedSing :: Sorted xs
    print xs
