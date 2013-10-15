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

_+_ : ℕ → ℕ → ℕ
Z + m = m
S n + m = S (n + m)

+assoc : ∀ n m o → ((n + m) + o) ≡ (n + (m + o))
+assoc Z m o = refl
+assoc (S n) m o = cong S (+assoc n m o)

ℕ+-IsSemigroup : IsSemigroup _≡_ _+_
ℕ+-IsSemigroup = record
    { isEquivalence = record
        { refl  = refl
        ; sym   = sym
        ; trans = trans
        }
    ; associativity = +assoc
    }

ℕ+-Semigroup : Semigroup _ _
ℕ+-Semigroup = record
    { Carrier = ℕ
    ; _≈_ = _≡_
    ; _∙_ = _+_
    ; isSemigroup = ℕ+-IsSemigroup
    }
