module Set where

open import Level
open import Function hiding (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record IsSet {c₁ ℓ : Level}
    (Elem : Set c₁)
    (_∈_ : {x : Elem} {X : Set c₁} → Rel Elem ℓ)
    : Set (suc (c₁ ⊔ ℓ))
