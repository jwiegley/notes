open import Data.Nat using (ℕ)

module Ledger (maxAccount : ℕ) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Function
open import Data.Maybe
open import Data.Nat using (zero; suc; _≡ᵇ_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; -_; _≤ᵇ_)
open import Data.Rational.Properties
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

Amount = ℚ

AccountId = ℕ

record Delta : Set where
  constructor MkDelta
  field
    xact : AccountId → AccountId → Amount

open Delta

infixr 1 _≡ᵈ_
_≡ᵈ_ : Delta → Delta → Set
MkDelta f ≡ᵈ MkDelta g = ∀ from to → f from to ≡ g from to

-- Delta is a semigroup
infixr 9 _∙_
_∙_ : Delta → Delta → Delta
MkDelta f ∙ MkDelta g =
  record { xact = λ from to →
    f from to + g from to
  }

∙-assoc : ∀ x y z → (x ∙ y) ∙ z ≡ᵈ x ∙ (y ∙ z)
∙-assoc x y z to from =
  +-assoc (xact x to from) (xact y to from) (xact z to from)

-- Delta is a monoid
ε : Delta
ε = record { xact = λ _ _ → 0ℚ }

∙-ε : ∀ x → ε ∙ x ≡ᵈ x
∙-ε x to from = +-identityˡ (xact x to from)

ε-∙ : ∀ x → x ∙ ε ≡ᵈ x
ε-∙ x to from = +-identityʳ (xact x to from)

-- Delta is a group
infix 5 _⁻¹
_⁻¹ : Delta → Delta
MkDelta f ⁻¹ =
  record { xact = λ from to → - (f from to) }

invert-left : ∀ x → (x ⁻¹) ∙ x ≡ᵈ ε
invert-left x to from = +-inverseˡ (xact x to from)

invert-right : ∀ x → x ∙ (x ⁻¹) ≡ᵈ ε
invert-right x to from = +-inverseʳ (xact x to from)

------------------------------------------------------------------------

transfer : AccountId → AccountId → Amount → Delta
transfer from to amt =
  record { xact = λ f t →
    if (from ≡ᵇ f) ∧ (to ≡ᵇ t) then amt else 0ℚ
  }

net : Delta → AccountId → AccountId → Amount
net (MkDelta f) x y with x ≡ᵇ y
... | true = 0ℚ
... | false = f x y - f y x

foldAccounts : ∀ {a : Set} → (a → AccountId → a) → a → a
foldAccounts {a} f z = go z maxAccount
  where
    mutual
      go : a → AccountId → a
      go z′ n = descend (f z′ n) n

      descend : a → AccountId → a
      descend z′ zero = z′
      descend z′ (suc n) = go z′ n

forallAccounts : (AccountId → Bool) → Bool
forallAccounts f = foldAccounts (λ p n → p ∧ f n) true

balance : Delta → AccountId → Amount
balance f acct = foldAccounts (λ acc n → net f n acct + acc) 0ℚ

------------------------------------------------------------------------

policy : ∀ {start : Delta} → List Delta → Set
policy {start} history =
    ∀ d → d ∈ inits (start ∷ history)
  → ∀ s → s ≡ foldl _∙_ ε d
  → forallAccounts (λ n → 0ℚ ≤ᵇ balance s n) ≡ true

settle
  : ∀ {start}
  → (d : Delta)
  → (ds : List Delta)
  → policy {start} ds
  → Maybe (policy {start} (ds ++ [ d ]))
settle {start} d ds P =
  let s = foldl _∙_ ε (start ∷ ds ++ [ d ]) in
  case forallAccounts (λ n → 0ℚ ≤ᵇ balance s n) of λ where
    true → just λ d₁ x s₁ x₁ → {!!}
    false → nothing
