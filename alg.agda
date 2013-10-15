module alg where

import Algebra.FunctionProperties as FunctionProperties
import Relation.Binary.EqReasoning as EqR

open import Data.Unit hiding (setoid)
open import Data.Empty
open import Data.Product
open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
    hiding (setoid; isEquivalence)

open FunctionProperties using (Op₁; Op₂)
open ≡-Reasoning

Associative : ∀ {c ℓ} {Carrier : Set c}
              → Rel Carrier ℓ → Op₂ Carrier → Set _
Associative _≈_ _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

record IsSemigroup {c ℓ} {Carrier : Set c}
    (_≈_ : Rel Carrier ℓ)
    (_∙_ : Op₂ Carrier)
    : Set (c ⊔ ℓ)
  where
    field
      isEquivalence : IsEquivalence _≈_
      associativity : Associative _≈_ _∙_

record Semigroup c ℓ : Set (suc (c ⊔ ℓ)) where
    infix  4 _≈_
    infixl 7 _∙_
    field
        Carrier     : Set c
        _≈_         : Rel Carrier ℓ
        _∙_         : Op₂ Carrier
        isSemigroup : IsSemigroup _≈_ _∙_

    open IsSemigroup isSemigroup public

    setoid : Setoid _ _
    setoid = record { isEquivalence = isEquivalence }

data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ

_≈ℕ_ : ℕ → ℕ → Set
Z ≈ℕ Z = ⊤
Z ≈ℕ S m = ⊥
S n ≈ℕ Z = ⊥
S n ≈ℕ S m = n ≈ℕ m

≈ℕ-refl : ∀ n → n ≈ℕ n
≈ℕ-refl Z = tt
≈ℕ-refl (S n) = ≈ℕ-refl n

≈ℕ-sym : ∀ n m → n ≈ℕ m → m ≈ℕ n
≈ℕ-sym Z Z = λ _ → tt
≈ℕ-sym Z (S m) = λ z → z
≈ℕ-sym (S n) Z = λ z → z
≈ℕ-sym (S n) (S m) = ≈ℕ-sym n m

≈ℕ-trans : ∀ n m o → n ≈ℕ m → m ≈ℕ o → n ≈ℕ o
≈ℕ-trans Z Z o = λ _ z → z
≈ℕ-trans Z (S m) o = λ ()
≈ℕ-trans (S n) Z o = λ ()
≈ℕ-trans (S n) (S m) Z = λ _ z → z
≈ℕ-trans (S n) (S m) (S o) = ≈ℕ-trans n m o

_+_ : ℕ → ℕ → ℕ
Z + m = m
S n + m = S (n + m)

+assoc : ∀ n m o → ((n + m) + o) ≈ℕ (n + (m + o))
+assoc Z Z Z = tt
+assoc Z Z (S o) = +assoc Z Z o
+assoc Z (S m) Z = +assoc Z m Z
+assoc Z (S m) (S o) = +assoc Z m (S o)
+assoc (S n) m Z = +assoc n m Z
+assoc (S n) m (S o) = +assoc n m (S o)

ℕ+-IsSemigroup : IsSemigroup _≈ℕ_ _+_
ℕ+-IsSemigroup = record
    { isEquivalence = record
        { refl  = λ {x} → ≈ℕ-refl x
        ; sym   = λ {i j} x → ≈ℕ-sym i j x
        ; trans = λ {i j k} x y → ≈ℕ-trans i j k x y
        }
    ; associativity = +assoc
    }

ℕ+-Semigroup : Semigroup _ _
ℕ+-Semigroup = record
    { Carrier = ℕ
    ; _≈_ = _≈ℕ_
    ; _∙_ = _+_
    ; isSemigroup = ℕ+-IsSemigroup
    }
