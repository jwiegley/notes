module Pipes where

open import Category.Functor
open import Category.Monad
open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Proxy (a' a b' b : Set) (m : Set -> Set) (r : Set) : Set where
    Request : a' → (a  → Proxy a' a b' b m r ) → Proxy a' a b' b m r
    Respond : b  → (b' → Proxy a' a b' b m r ) → Proxy a' a b' b m r
    M       :      (m   (Proxy a' a b' b m r)) → Proxy a' a b' b m r
    Pure    : r                                → Proxy a' a b' b m r
