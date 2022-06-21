import Data.Nat using (ℕ)

module Ledger (maxAccount : Data.Nat.ℕ) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool hiding (_≤_; _≟_)
open import Data.List
open import Data.List.Membership.Propositional using (_∈_)
open import Function
open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.Maybe
open import Data.Product
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; -_; _≤ᵇ_; _≤_)
open import Data.Rational.Properties hiding (_≟_)
open import Relation.Nullary using (does; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

Amount = ℚ

AccountId = Fin maxAccount

Delta : Set
Delta = AccountId → AccountId → Amount

infixr 1 _≡ᵈ_
_≡ᵈ_ : Delta → Delta → Set
f ≡ᵈ g = ∀ from to → f from to ≡ g from to

-- Delta is a semigroup
infixr 9 _∙_
_∙_ : Delta → Delta → Delta
f ∙ g = λ from to → f from to + g from to

∙-assoc : ∀ x y z → (x ∙ y) ∙ z ≡ᵈ x ∙ (y ∙ z)
∙-assoc x y z to from =
  +-assoc (x to from) (y to from) (z to from)

-- Delta is a monoid
ε : Delta
ε _ _ = 0ℚ

∙-ε : ∀ x → ε ∙ x ≡ᵈ x
∙-ε x to from = +-identityˡ (x to from)

ε-∙ : ∀ x → x ∙ ε ≡ᵈ x
ε-∙ x to from = +-identityʳ (x to from)

-- Delta is a group
infix 5 _⁻¹
_⁻¹ : Delta → Delta
f ⁻¹ = λ from to → - (f from to)

invert-left : ∀ x → (x ⁻¹) ∙ x ≡ᵈ ε
invert-left x to from = +-inverseˡ (x to from)

invert-right : ∀ x → x ∙ (x ⁻¹) ≡ᵈ ε
invert-right x to from = +-inverseʳ (x to from)

------------------------------------------------------------------------

transfer : AccountId → AccountId → Amount → Delta
transfer from to amt = λ f t →
  if does (from ≟ f) ∧ does (to ≟ t) then amt else 0ℚ

net : Delta → AccountId → AccountId → Amount
net f x y = f x y - f y x

balance : Delta → AccountId → Amount
balance f acct = foldr _+_ 0ℚ (tabulate (net f acct))

------------------------------------------------------------------------

settled : ∀ {start : AccountId → Amount} → List Delta → Set
settled {start} history =
    ∀ f → f ∈ scanl (λ ldg f acct → ldg acct + f acct)
                    start (Data.List.map balance history)
  → ∀ n → 0ℚ ≤ f n

------------------------------------------------------------------------

Transaction : Set
Transaction = AccountId × AccountId × Amount

denote : Transaction → Delta
denote = λ (from , to , amt) → transfer from to amt

settle
  : ∀ (accounts : AccountId → Amount)
  → (xact : Transaction)
  → Relation.Nullary.Dec (settled {accounts} [ denote xact ])
settle = {!!}

record Ledger : Set where
  field
    genesis : AccountId → Amount
    history : List Transaction

    .is-settled : settled {genesis} (Data.List.map denote history)

    -- caching the application of transactions
    accounts : AccountId → Amount

    .accounts-sound : ∀ acct → 0ℚ ≤ accounts acct

open Ledger

xfer : AccountId → AccountId → Amount → Transaction
xfer from to amt = (from , to , amt)

xfer-homomorphism : ∀ from to amt → denote (xfer from to amt) ≡ transfer from to amt
xfer-homomorphism _ _ _ = refl

-- accounts-homomorphism : ∀ from to amt → denote (accounts acct) ≡ balance
-- accounts-homomorphism _ _ _ = refl

ledger-denote : Ledger → Delta
ledger-denote = foldl _∙_ ε ∘ Data.List.map denote ∘ history
