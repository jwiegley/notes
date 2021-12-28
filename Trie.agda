{-# OPTIONS --safe --without-K #-}

module Trie where

open import Level
open import Function using (_∘_)
open import Data.Product as × using (_,_; _×_; uncurry; curry)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Relation.Binary

open import Misc
open import Shape

private variable
  a b ℓ : Level
  A B C D : Set a
  s t : Shape

infix 6 _▿_
data T (A : Set a) : Shape → Set a where
  1̇ : T A `⊥
  I : A → T A `⊤
  _▿_ : T A s → T A t → T A (s `⊎ t)
  ▽ : T (T A t) s → T A (s `× t)

open import Data.Vec as v using (Vec; []; _∷_; _++_; concat; splitAt; group)

-- pattern [_] x = x ∷ []

vec : T A s → Vec A (size s)
vec 1̇ = []
vec (I x) = x ∷ []
vec (u ▿ v) = vec u ++ vec v
vec (▽ us) = concat (v.map vec (vec us))

open import Relation.Binary.PropositionalEquality using (refl)

open ++⁻¹ ; open concat⁻¹

trie : Vec A (size s) → T A s
trie {s = `⊥} [] = 1̇
trie {s = `⊤} (x ∷ []) = I x
trie {s = s `⊎ t} xs =
  let ys , zs = ++⁻¹ xs in trie ys ▿ trie zs
trie {s = s `× t} xs =
  let xss = concat⁻¹ xs in ▽ (trie (v.map trie xss))
