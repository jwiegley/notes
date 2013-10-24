module alg where

import Algebra.FunctionProperties as FunctionProperties
import Relation.Binary.EqReasoning as EqR

open import Data.Unit hiding (setoid)
open import Data.Empty
open import Data.Nat hiding (_⊔_; suc)
open import Data.Product
open import Level
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
    hiding (setoid; isEquivalence)

open import nat

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

ℕ+-IsSemigroup : IsSemigroup _≡_ _+_
ℕ+-IsSemigroup = record
    { isEquivalence = record
        { refl  = refl
        ; sym   = sym
        ; trans = trans
        }
    ; associativity = lemma-+assoc
    }

ℕ+-Semigroup : Semigroup _ _
ℕ+-Semigroup = record
    { Carrier = ℕ
    ; _≈_ = _≡_
    ; _∙_ = _+_
    ; isSemigroup = ℕ+-IsSemigroup
    }

record IsMonoid {c ℓ} {Carrier : Set c}
    (ε : Carrier)
    (_≈_ : Rel Carrier ℓ)
    (_∙_ : Op₂ Carrier)
    : Set (c ⊔ ℓ)
  where
    field
      isSemigroup   : IsSemigroup _≈_ _∙_
      left-identity : {n : Carrier} → _∙_ ε n ≈ n
      right-identity : {n : Carrier} → _∙_ n ε ≈ n

record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
    infix  4 _≈_
    infixl 7 _∙_
    field
        Carrier : Set c
        ε       : Carrier
        _≈_     : Rel Carrier ℓ
        _∙_     : Op₂ Carrier
        isMonoid : IsMonoid ε _≈_ _∙_

    open IsMonoid isMonoid public

ℕ+-IsMonoid : IsMonoid 0 _≡_ _+_
ℕ+-IsMonoid = record
    { isSemigroup = ℕ+-IsSemigroup
    ; left-identity = λ {n} → refl
    ; right-identity = λ {n} → lemma-+0 n
    }

ℕ+-Monoid : Monoid _ _
ℕ+-Monoid = record
    { Carrier = ℕ
    ; ε = 0
    ; _≈_ = _≡_
    ; _∙_ = _+_
    ; isMonoid = ℕ+-IsMonoid
    }
