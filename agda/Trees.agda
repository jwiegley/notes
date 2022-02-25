module Trees where

open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Level using (Level; 0ℓ)
import Data.List
import Data.List.Membership.Propositional
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

private variable
  k v : Set

-- k → v

-- k → v × ℕ

-- ∃ λ u → v ≡ Maybe u → (k → v × ℕ)

-- Map k u

------------------------------------------------------------------------

Finite : ℕ → Pred k 0ℓ → Set
Finite n P = ∃ P ↔ Fin n

Finite-add : ∀ {n : ℕ} {P : Pred k 0ℓ}
  → Finite n P
  → {x : k} → x ∉ P
  → Finite (suc n) (P ∪ ｛ x ｝)
Finite-add F x∉P = {!!}

Finite-drop : ∀ {n : ℕ} {P : Pred k 0ℓ}
  → Finite (suc n) P
  → {x : k} → x ∈ P
  → Finite n (P ∩ ∁ ｛ x ｝)
Finite-drop F x∈P = {!!}

record α (n : ℕ) (k v : Set) : Set₁ where
  constructor mkα
  field
    P : Pred k 0ℓ
    F : Finite n P
    f : ∃ P → v

-- α : ℕ → Set → Set → Set₁
-- α n k v = ∃ λ (P : k → Set) → Finite n P → ∃ P → v

present : ∀ {n : ℕ} → α n k v → Pred k 0ℓ
present = α.P

insert : ∀ {n : ℕ} (x : k)
  → (∃ λ (m  : α      n  k v)  → ¬ present m  x)
  → v
  → (∃ λ (m′ : α (suc n) k v) →   present m′ x)
insert x (mkα P F f , ¬present) v =
  mkα (P ∪ ｛ x ｝) (Finite-add F ¬present)
    (λ { (x′ , inj₁ l)    → f (x′ , l)
       ; (.x , inj₂ refl) → v })
    , inj₂ refl

delete : ∀ {n : ℕ} (x : k)
  → (∃ λ (m  : α (suc n) k v) →   present m  x)
  → (∃ λ (m′ : α      n  k v)  → ¬ present m′ x)
delete x (mkα P F f , is-present) =
  mkα (P ∩ ∁ ｛ x ｝) (Finite-drop F is-present)
    (λ { (x′ , Px′ , x≢x′) → f (x′ , Px′) })
    , λ z → proj₂ z refl

lemma : ∀ {n : ℕ} (m : α n k v) (x : k) P (u : v)
   → proj₁ (delete x (insert x (m , P) u)) ≡ m
lemma (mkα P₁ F f) x P u = {!!}

------------------------------------------------------------------------
-- Maps

-- A finite function, if it were written as a set of pairs, that set would be
-- finite.
-- Predicate : k → Set
-- Predicate = {!!}

FinFunc : Set → Set → Set
FinFunc k v = k → v

-- keys : {k v : Set} → FinFunc k v → Pred k Level.zero
-- keys = Is-just ∘_

-- insert : FinFunc k v → k → v → FinFunc k v
-- insert m k v k′ = {!!}

_∧_ : Set → Set → Set
P ∧ Q = P × Q

-- The size of a map is the cardinality of its key set
-- size : FinFunc k v → ℕ → Set
-- size {k = k} {v = v} m sz =
--   ∃ λ (xs : Data.List.List k) →
--     Irrelevant (Data.List.Membership.Propositional._∈ xs) →
--     (sz ≡ Data.List.length xs) ∧
--     (∀ x → x Data.List.Membership.Propositional.∈ xs ↔ x ∈ keys m)

------------------------------------------------------------------------

-- repr : Map k v

-- denote : Map k v -> k → Maybe v

------------------------------------------------------------------------
-- Balanced FinFuncs

CostFinFunc : Set → Set → Set
CostFinFunc k v = k → (Maybe v × ℕ)

-- forget : CostFinFunc k v → FinFunc k v
-- forget m k = proj₁ (m k)

-- balanced : Set₁
-- balanced = ∀ {k v} (m : CostFinFunc k v) →
--   ∀ x v n sz → m x ≡ (v , n) → size (forget m) sz → 2 ^ n ≤ sz

------------------------------------------------------------------------
-- Trees

------------------------------------------------------------------------
-- Balanced Trees

-- steps : Map k v → k → ℕ → Set₁
-- steps m sz = {!!}

-- -- Return the number of elements in the tree
-- size : Map k v → ℕ → Set₁
-- size m sz = {!!}
--   -- ∀ k → ∃ λ x → m k ≡ just x
