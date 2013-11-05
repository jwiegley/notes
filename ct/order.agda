module order where

open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import nat
open ≡-Reasoning

≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-antisym : ∀ m n → m ≤ n → n ≤ m → m ≡ n
≤-antisym .0 .0 z≤n z≤n = refl
≤-antisym .(suc m) .(suc n) (s≤s {m} {n} h₁) (s≤s h₂) =
    sym (cong suc (≤-antisym n m h₂ h₁))

≤-trans : ∀ k m n → k ≤ m → m ≤ n → k ≤ n
≤-trans .0 m n z≤n h₂ = z≤n
≤-trans .(suc m) .(suc n) .(suc n₁) (s≤s {m} {n} h₁) (s≤s {.n} {n₁} h₂) =
    s≤s (≤-trans m n n₁ h₁ h₂)

≤-total : ∀ m n → m ≤ n ⊎ n ≤ m
≤-total zero n = inj₁ z≤n
≤-total (suc m) zero = inj₂ z≤n
≤-total (suc m) (suc n) with ≤-total m n
≤-total (suc m) (suc n) | inj₁ x = inj₁ (s≤s x)
≤-total (suc m) (suc n) | inj₂ y = inj₂ (s≤s y)

n≤n+ : ∀ n k → n ≤ k + n
n≤n+ zero k = z≤n
n≤n+ (suc n) k = subst (λ x → suc n ≤ x) (lemma-+sucgr k n) (s≤s (n≤n+ n k))

m+≤n+′ : ∀ m n k → m ≤ n → m + k ≤ n + k
m+≤n+′ .0 n k z≤n = n≤n+ k n
m+≤n+′ .(suc m) .(suc n) k (s≤s {m} {n} h) = s≤s (m+≤n+′ m n k h)

m+≤n+ : ∀ m n k → m ≤ n → k + m ≤ k + n
m+≤n+ m n zero h = h
m+≤n+ m n (suc k) h = s≤s (m+≤n+ m n k h)

mk≤nk : ∀ m n k → m ≤ n → ¬ (k ≡ 0) → m * k ≤ n * k
mk≤nk .zero _ _ z≤n _ = z≤n
mk≤nk (suc m) (suc n) k (s≤s p) q = m+≤n+ (m * k) (n * k) k (mk≤nk m n k p q)

unprovable : ∀ {ℓ} {p : Set ℓ} → (¬ (¬ p)) ≡ p
unprovable = {!!}
