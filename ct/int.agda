module int where

open import Data.Nat
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

lemma-+0 : ∀ n → n + 0 ≡ n
lemma-+0 zero = refl
lemma-+0 (suc n) = cong suc (lemma-+0 n)

lemma-+suc : ∀ a b → suc a + b ≡ a + suc b
lemma-+suc zero b = refl
lemma-+suc (suc a) b = cong suc (lemma-+suc a b)

lemma-+assoc : ∀ n m o → (n + m) + o ≡ n + (m + o)
lemma-+assoc zero m o = refl
lemma-+assoc (suc n) m o = cong suc (lemma-+assoc n m o)

lemma-+comm : ∀ n m → n + m ≡ m + n
lemma-+comm zero zero = refl
lemma-+comm zero (suc m) = cong suc (sym (lemma-+0 m))
lemma-+comm (suc n) m = trans (cong suc (lemma-+comm n m)) (lemma-+suc m n)

lemma-+sucgr : ∀ a b → suc (a + b) ≡ a + suc b
lemma-+sucgr zero b = refl
lemma-+sucgr (suc a) b = cong suc (lemma-+sucgr a b)

lemma-+shuffle : ∀ n m o → n + (m + o) ≡ m + (n + o)
lemma-+shuffle zero m o = refl
lemma-+shuffle (suc n) m o =
    trans (cong suc (lemma-+shuffle n m o)) (lemma-+sucgr m (n + o))

lemma-+distrib : ∀ n m o p → (n + m) + (o + p) ≡ (n + o) + (m + p)
lemma-+distrib zero m o p = lemma-+shuffle m o p
lemma-+distrib (suc n) m o p = cong suc (lemma-+distrib n m o p)

lemma-*ldist : ∀ n m o → n * (m + o) ≡ n * m + n * o
lemma-*ldist zero _ _ = refl
lemma-*ldist (suc n) m o =
    begin
        suc n * (m + o)
    ≡⟨ refl ⟩
        m + o + n * (m + o)
    ≡⟨ cong (_+_ (m + o)) (lemma-*ldist n m o) ⟩
        m + o + (n * m + n * o)
    ≡⟨ sym (lemma-+assoc (m + o) (n * m) (n * o)) ⟩
        m + o + n * m + n * o
    ≡⟨ lemma-+assoc (m + o) (n * m) (n * o) ⟩
        (m + o) + (n * m + n * o)
    ≡⟨ lemma-+distrib m o (n * m) (n * o) ⟩
        m + n * m + (o + n * o)
    ≡⟨ refl ⟩
        suc n * m + (o + n * o)
    ≡⟨ refl ⟩
        suc n * m + suc n * o
    ∎

lemma-0* : ∀ n → zero * n ≡ zero
lemma-0* _ = refl

lemma-*0 : ∀ n → n * zero ≡ zero
lemma-*0 zero = refl
lemma-*0 (suc n) = trans (lemma-*0 n) (lemma-0* n)

lemma-+*0 : ∀ n m → n * 0 + m * 0 ≡ 0
lemma-+*0 zero m = lemma-*0 m
lemma-+*0 (suc n) zero = lemma-+*0 n zero
lemma-+*0 (suc n) (suc m) = lemma-+*0 n m

lemma-*suc : ∀ n m → n * suc m ≡ n + n * m
lemma-*suc zero m = refl
lemma-*suc (suc n) m =
    cong suc (trans (cong (_+_ m) (lemma-*suc n m))
        (lemma-+shuffle m n (n * m)))

lemma-*rdist : ∀ n m o → (m + o) * n ≡ m * n + o * n
lemma-*rdist zero m o =
    begin
        (m + o) * 0
    ≡⟨ lemma-*0 (m + o) ⟩
        zero
    ≡⟨ sym (lemma-+*0 m o) ⟩
        m * 0 + o * 0
    ∎
lemma-*rdist (suc n) m o =
    begin
        (m + o) * suc n
    ≡⟨ lemma-*suc (m + o) n ⟩
        m + o + (m + o) * n
    ≡⟨ cong (_+_ (m + o)) (lemma-*rdist n m o) ⟩
        m + o + (m * n + o * n)
    ≡⟨ lemma-+distrib m o (m * n) (o * n) ⟩
        (m + m * n) + (o + o * n)
    ≡⟨ sym (cong (_+_ (m + m * n)) (lemma-*suc o n)) ⟩
        (m + m * n) + o * suc n
    ≡⟨ lemma-+comm (m + m * n) (o * suc n) ⟩
        o * suc n + (m + m * n)
    ≡⟨ sym (cong (_+_ (o * suc n)) (lemma-*suc m n)) ⟩
        o * suc n + m * suc n
    ≡⟨ lemma-+comm (o * suc n) (m * suc n) ⟩
        m * suc n + o * suc n
    ∎

lemma-∸assoc : ∀ n m o → (n ∸ m) ∸ o ≡ n ∸ (m ∸ o)
lemma-∸assoc zero zero o = {!!}
lemma-∸assoc zero (suc m) o = {!!}
lemma-∸assoc (suc n) m o = {!!}

lemma-∸sucgr : ∀ a b → suc (a ∸ b) ≡ a ∸ suc b
lemma-∸sucgr zero b = {!!}
lemma-∸sucgr (suc a) b = {!!}

lemma-∸shuffle : ∀ n m o → n ∸ (m ∸ o) ≡ m ∸ (n ∸ o)
lemma-∸shuffle zero m o = {!!}
lemma-∸shuffle (suc n) m o = {!!}

lemma-∸distrib : ∀ n m o p → (n ∸ m) ∸ (o ∸ p) ≡ (n ∸ o) ∸ (m ∸ p)
lemma-∸distrib zero m o p = {!!}
lemma-∸distrib (suc n) m o p = {!!}

-- lemma-*ldist∸ : ∀ n m o → n * (m ∸ o) ≡ n * m ∸ n * o
-- lemma-*ldist∸ zero _ _ = refl
-- lemma-*ldist∸ (suc n) m o =
--     begin
--         suc n * (m ∸ o)
--     ≡⟨ refl ⟩
--         m ∸ o ∸ n * (m ∸ o)
--     ≡⟨ cong (_∸_ (m ∸ o)) (lemma-*ldist∸ n m o) ⟩
--         m ∸ o ∸ (n * m ∸ n * o)
--     ≡⟨ sym (lemma-∸assoc (m ∸ o) (n * m) (n * o)) ⟩
--         m ∸ o ∸ n * m ∸ n * o
--     ≡⟨ lemma-∸assoc (m ∸ o) (n * m) (n * o) ⟩
--         (m ∸ o) ∸ (n * m ∸ n * o)
--     ≡⟨ lemma-∸distrib m o (n * m) (n * o) ⟩
--         m ∸ n * m ∸ (o ∸ n * o)
--     ≡⟨ refl ⟩
--         suc n * m ∸ (o ∸ n * o)
--     ≡⟨ refl ⟩
--         suc n * m ∸ suc n * o
--     ∎

lemma-∸*0 : ∀ n m → n * 0 ∸ m * 0 ≡ 0
lemma-∸*0 zero m = {!!}
lemma-∸*0 (suc n) zero = {!!}
lemma-∸*0 (suc n) (suc m) = {!!}

lemma-*suc∸ : ∀ n m → n * suc m ≡ n ∸ n * m
lemma-*suc∸ zero m = refl
lemma-*suc∸ (suc n) m = {!!}

lemma-*assoc : ∀ n m o → n * (m * o) ≡ (n * m) * o
lemma-*assoc zero _ _ = refl
lemma-*assoc (suc n) m o =
    begin
        suc n * (m * o)
    ≡⟨ refl ⟩
        m * o + n * (m * o)
    ≡⟨ cong (_+_ (m * o)) (lemma-*assoc n m o) ⟩
        m * o + (n * m) * o
    ≡⟨ sym (lemma-*rdist o m (n * m)) ⟩
        (m + n * m) * o
    ≡⟨ refl ⟩
        (suc n * m) * o
    ∎

lemma-chris : ∀ a b c d → a * d ≡ b * c → a ‌≢ c → b ≢ d
              → (a ∸ c) * b ≡ a * (b ∸ d)
lemma-chris a b c d h₁ h₂ h₃ =
    begin
        (a ∸ c) * b
    ≡⟨ {!rdistrib!} ⟩
        a * b ∸ c * b
    ≡⟨ {!*comm!} ⟩
        a * b ∸ b * c
    ≡⟨ {!trans h₁!} ⟩
        a * b ∸ a * d
    ≡⟨ {!ldistrib!} ⟩
        a * (b ∸ d)
    ∎

-- a/b = c/d => cb = da => cb - cd = da - cd => 

-- c(b-d) = d(a-c) => c/d = (a-c)/(b-d).
