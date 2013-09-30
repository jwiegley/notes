module Collatz where

open import Coinduction
open import Data.Nat hiding (_+_; _*_)
open import Data.Fin hiding (_+_; fromℕ; toℕ)
open import Data.Bin hiding (suc)
open import Data.Maybe
open import Data.Product
open import Data.List as List
open import Data.Colist

data Parity : Bin → Set where
  even : ∀ n → Parity (n *2)
  odd  : ∀ n → Parity (n *2+1)

parity : ∀ n → Parity n
parity 0# = even 0#
parity ([] 1#) = odd 0#
parity ((zero     ∷ bs) 1#) = even (bs 1#)
parity ((suc zero ∷ bs) 1#) = odd  (bs 1#)
parity ((suc (suc ()) ∷ bs) 1#)

toList : ∀ {a} {A : Set a} → ℕ → Colist A → List A
toList zero xs = []
toList (suc n) [] = []
toList (suc n) (x ∷ xs) = x ∷ toList n (♭ xs)

unfoldr : ∀ {a b} {A : Set a} {B : Set b} → (B → Maybe (A × B)) → B → Colist A
unfoldr f b with f b
unfoldr f b | just (a , b′) = a ∷ ♯ unfoldr f b′
unfoldr f b | nothing = []

one : Bin
one = fromℕ 1

three : Bin
three = fromℕ 3

collatz : Bin → Colist Bin
collatz = unfoldr gen
  where
  next : Bin → Bin
  next x with parity x
  next ._ | even n = n
  next ._ | odd  n = three * (n *2+1) + one

  gen : Bin → Maybe (Bin × Bin)
  gen 0#      = nothing
  gen ([] 1#) = just (one , 0#)
  gen x       = just (x , next x)


conjecture : ∀ n → Finite (collatz n)
conjecture n = {!!} -- you fill this in