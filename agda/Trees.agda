module Trees where

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Nat
open import Data.Maybe
open import Data.Sum
open import Data.Product
open import Function
open import Algebra.Structures
open import Function.Related.TypeIsomorphisms
open import Level using (Level; 0ℓ)
import Data.List
import Data.List.Membership.Propositional
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_]; Extensionality)
open ≡-Reasoning
open import Axiom.Extensionality.Propositional
postulate extensionality : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

private variable
  k v : Set

-- k → v

-- k → v × ℕ

-- ∃ λ u → v ≡ Maybe u → (k → v × ℕ)

-- Map k u

record α (k v : Set) : Set₁ where
  constructor mkα
  field
    f : Pred (k × v) 0ℓ

present : α k v → Pred k 0ℓ
present m = λ i → ∃ λ x → α.f m (i , x)

all-keys : k → Pred (k × v) 0ℓ
all-keys i = λ (j , y) → i ≡ j

insert : ∀ {i : k}
  → v
  → (∃ λ (m  : α k v) → ¬ present m  i)
  → (∃ λ (m′ : α k v) →   present m′ i)
insert {i = i} x (mkα f , ¬present) =
  mkα (f ∪ ｛ ( i , x )  ｝) , x , inj₂ refl

delete : ∀ {i : k}
  → (∃ λ (m  : α k v) →   present m  i)
  → (∃ λ (m′ : α k v) → ¬ present m′ i)
delete {i = i} (mkα f , is-present) =
  mkα (f ∩ ∁ (all-keys i)) , λ (_ , _ , k) → k refl

{-
------------------------------------------------------------------------

Finite : ℕ → Pred k 0ℓ → Set
Finite n P = ∃ P ↔ Fin n

Finite-add : ∀ {n : ℕ} {P : Pred k 0ℓ}
  → Finite n P
  → {x : k} → x ∉ P
  → Finite (suc n) (P ∪ ｛ x ｝)
Finite-add
  record { f       = f
         ; f⁻¹     = f⁻¹
         ; cong₁   = cong₁
         ; cong₂   = cong₂
         ; inverse = inverse
         } {x} x∉P =
  record { f       = {!!}
         ; f⁻¹     = {!!}
         ; cong₁   = {!!}
         ; cong₂   = {!!}
         ; inverse = (λ x₁ → {!!}) , λ x₁ → {!!} }

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

cong₃ : ∀ {ℓa ℓb ℓc ℓ′} {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓ′}
          (f : A → B → C → D) {x y u v i j}
  → x ≡ y → u ≡ v → i ≡ j → f x u i ≡ f y v j
cong₃ f refl refl refl = refl

_∧_ : Set → Set → Set
P ∧ Q = P × Q

record _≈_ {n : ℕ} (p q : α n k v) : Set₁ where
  constructor α≈
  field
    P≈ : ∀ (x : k) → α.P p x ↔ α.P q x
    F≈ : ∀ x P → Inverse.f (α.F p) (x , P) ≡ Inverse.f (α.F q) (x , Inverse.f (P≈ x) P)
    -- F⁻¹≈ : ∀ n → Inverse.f⁻¹ (α.F p) n ≡ Inverse.f⁻¹ (α.F {!!}) n
    f≈ : ∀ x P → α.f p (x , P) ≡ α.f q (x , Inverse.f (P≈ x) P)

present : ∀ {n : ℕ} → α n k v → Pred k 0ℓ
present = α.P

insert : ∀ {n : ℕ} {x : k}
  → v
  → (∃ λ (m  : α      n  k v)  → ¬ present m  x)
  → (∃ λ (m′ : α (suc n) k v) →   present m′ x)
insert {x = x} v (mkα P F f , ¬present) =
  mkα (P ∪ ｛ x ｝) (Finite-add F ¬present)
    (λ { (x′ , inj₁ l)    → f (x′ , l)
       ; (.x , inj₂ refl) → v })
    , inj₂ refl

delete : ∀ {n : ℕ} {x : k}
  → (∃ λ (m  : α (suc n) k v) →   present m  x)
  → (∃ λ (m′ : α      n  k v)  → ¬ present m′ x)
delete {x = x} (mkα P F f , is-present) =
  mkα (P ∩ ∁ ｛ x ｝) (Finite-drop F is-present)
    (λ { (x′ , Px′ , x≢x′) → f (x′ , Px′) })
    , λ z → proj₂ z refl

-- _≈̂_ : {!!}
-- _≈̂_ = _≡_ on proj₁

lemma : ∀ {n : ℕ} (x : k) (e : ∃ λ (m : α n  k v)  → ¬ present m x) (u : v)
   → proj₁ (delete {x = x} (insert u e)) ≡ proj₁ e
lemma {n} x (mkα P F f , ¬Px) u =
  begin
    proj₁ (delete (insert u (mkα P F f , ¬Px)))
  ≡⟨⟩
    mkα
      (λ x₁ → (P x₁ ⊎ x ≡ x₁) × (x ≢ x₁))
      _
      (λ { (x′ , Px′ , x≢x′)
             → (λ { (x′ , inj₁ l) → f (x′ , l) ; (_ , inj₂ refl) → u })
               (x′ , Px′)
         })
  ≡⟨ cong₃ (λ x₁ x₂ x₃ → mkα x₁ x₂ {!!})
           helper
           {!!}
           {!!} ⟩
    mkα P F f
  ∎
  where
  helper : (λ x₁ → (P x₁ ⊎ x ≡ x₁) × x ≢ x₁) ≡ P
  helper = extensionality λ x₁ →
    begin
      ((P x₁ ⊎ x ≡ x₁) × x ≢ x₁)
    -- ≡⟨ trans (×-distribˡ-⊎ _ ? (x ≡ x₁) (x ≢ x₁)) ? ⟩
    ≡⟨ {!!} ⟩
      ((P x₁ × x ≢ x₁) ⊎ (x ≡ x₁ × x ≢ x₁))
    ≡⟨ {!!} ⟩
      ((P x₁ × x ≢ x₁) ⊎ ⊥)
    ≡⟨ {!!} ⟩
      (P x₁ × x ≢ x₁)
    ≡⟨ {!!} ⟩
      {!!}
    ≡⟨⟩
      P x₁
    ∎

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
-}
