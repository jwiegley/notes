module nat where

open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

lemma-indℕ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
lemma-indℕ P P0 istep zero    = P0
lemma-indℕ P P0 istep (suc n) = istep n (lemma-indℕ P P0 istep n)

lemma-suc= : ∀ a b → suc a ≡ suc b → a ≡ b
lemma-suc= x .x refl = refl

lemma-+= : ∀ n m o → m ≡ o → n + m ≡ n + o
lemma-+= n m o h = cong (_+_ n) h

lemma-+0 : ∀ n → n + zero ≡ n
lemma-+0 zero = refl
lemma-+0 (suc n) = cong suc (lemma-+0 n)

lemma-0+ : ∀ n → zero + n ≡ n
lemma-0+ zero = refl
lemma-0+ (suc n) = refl

lemma-+1 : ∀ n → n + suc zero ≡ suc n
lemma-+1 zero = refl
lemma-+1 (suc n) = cong suc (lemma-+1 n)

lemma-+suc : ∀ a b → suc a + b ≡ a + suc b
lemma-+suc zero b = refl
lemma-+suc (suc a) b = cong suc (lemma-+suc a b)

lemma-+sucgl : ∀ a b → suc (a + b) ≡ suc a + b
lemma-+sucgl zero b = refl
lemma-+sucgl (suc a) b = refl

lemma-+sucgr : ∀ a b → suc (a + b) ≡ a + suc b
lemma-+sucgr zero b = refl
lemma-+sucgr (suc a) b = cong suc (lemma-+sucgr a b)

lemma-+sucsuc : ∀ a b → suc a + suc b ≡ suc (suc (a + b))
lemma-+sucsuc zero b = refl
lemma-+sucsuc (suc a) b = cong suc (cong suc (sym (lemma-+sucgr a b)))

lemma-+comm : ∀ n m → n + m ≡ m + n
lemma-+comm zero zero = refl
lemma-+comm zero (suc m) = cong suc (sym (lemma-+0 m))
lemma-+comm (suc n) m = trans (cong suc (lemma-+comm n m)) (lemma-+suc m n)

lemma-+assoc : ∀ n m o → (n + m) + o ≡ n + (m + o)
lemma-+assoc zero m o = refl
lemma-+assoc (suc n) m o = cong suc (lemma-+assoc n m o)

lemma-+shuffle : ∀ n m o → n + (m + o) ≡ m + (n + o)
lemma-+shuffle zero m o = refl
lemma-+shuffle (suc n) m o =
    trans (cong suc (lemma-+shuffle n m o)) (lemma-+sucgr m (n + o))

lemma-+distrib : ∀ n m o p → (n + m) + (o + p) ≡ (n + o) + (m + p)
lemma-+distrib zero m o p = lemma-+shuffle m o p
lemma-+distrib (suc n) m o p = cong suc (lemma-+distrib n m o p)

lemma-0* : ∀ n → zero * n ≡ zero
lemma-0* _ = refl

lemma-*0 : ∀ n → n * zero ≡ zero
lemma-*0 zero = refl
lemma-*0 (suc n) = trans (lemma-*0 n) (lemma-0* n)

lemma-+*0 : ∀ n m → n * 0 + m * 0 ≡ 0
lemma-+*0 zero m = lemma-*0 m
lemma-+*0 (suc n) zero = lemma-+*0 n zero
lemma-+*0 (suc n) (suc m) = lemma-+*0 n m

lemma-1* : ∀ n → suc zero * n ≡ n
lemma-1* = lemma-+0

lemma-*1 : ∀ n → n * suc zero ≡ n
lemma-*1 zero = refl
lemma-*1 (suc n) = cong suc (lemma-*1 n)

lemma-*2 : ∀ n → n + n ≡ n * suc (suc zero)
lemma-*2 zero = refl
lemma-*2 (suc n) =
    cong suc (trans (sym (lemma-+suc n n)) (cong suc (lemma-*2 n)))

lemma-+0*1 : ∀ n → n + 0 ≡ n * 1
lemma-+0*1 zero = refl
lemma-+0*1 (suc n) = cong suc (lemma-+0*1 n)

lemma-*suc : ∀ n m → n * suc m ≡ n + n * m
lemma-*suc zero m = refl
lemma-*suc (suc n) m =
    cong suc (trans (cong (_+_ m) (lemma-*suc n m))
        (lemma-+shuffle m n (n * m)))

lemma-*comm : ∀ n m → n * m ≡ m * n
lemma-*comm zero m = sym (lemma-*0 m)
lemma-*comm (suc n) m =
    sym (trans (lemma-*suc m n) (sym (cong (_+_ m) (lemma-*comm n m))))

lemma-*comm2 : ∀ n m → n * m ≡ m * n
lemma-*comm2 zero m = sym (lemma-*0 m)
lemma-*comm2 (suc n) m =
    begin
        suc n * m
    ≡⟨ refl ⟩
        m + n * m
    ≡⟨ cong (_+_ m) (lemma-*comm2 n m) ⟩
        m + m * n
    ≡⟨ sym (lemma-*suc m n) ⟩
        m * suc n
    ∎

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
