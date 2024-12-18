module nat where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- prime : ∀ n → Set
-- prime zero = ⊥
-- prime (suc zero) = ⊥
-- prime (suc (suc zero)) = ⊤
-- prime (suc n) = prime n

-- goldbach : (n p q : ℕ) → n > 2 → even n
--            → ∃₂ (λ p q → prime p × prime q × p + q ≡ n)
-- goldbach zero p q () _
-- goldbach (suc n) p q h₁ h₂ = {!!} , {!!}

-- data Divides : ℕ → ℕ → Set where
--     divides-by-1 : (n : ℕ) → Divides n 1

-- DividesDecidable : Set
-- DividesDecidable = ∀ n m → Dec (Divides n m)

-- divides' : DividesDecidable
-- divides' n zero = no (λ ())
-- divides' n (suc zero) = yes (divides-by-1 n)
-- divides' n m = {!!}

-- divisible : ∀ n m → ∃₂ (λ q r → n ≡ m * q + r)
-- divisible zero zero = zero , zero , refl
-- divisible zero (suc m) = {!!}
-- divisible (suc n) zero = n , suc n , refl
-- divisible (suc n) (suc m) = {!!}

lemma-indℕ : (P : ℕ → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
lemma-indℕ P P0 istep zero    = P0
lemma-indℕ P P0 istep (suc n) = istep n (lemma-indℕ P P0 istep n)

lemma-suc= : ∀ a b → a ≡ b → suc a ≡ suc b
lemma-suc= n .n refl = refl

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

lemma-+sucsucl : ∀ n m → suc (suc (n + m)) ≡ suc n + suc m
lemma-+sucsucl n m = cong suc (lemma-+sucgr n m)

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

-- lemma-+distrib : ∀ n m o p → (n + m) + (o + p) ≡ (n + o) + (m + p)
-- lemma-+distrib zero m o p = lemma-+shuffle m o p
-- lemma-+distrib (suc n) m o p = cong suc (lemma-+distrib n m o p)

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

lemma-*over+ : ∀ a b c d → (a + b) * (c + d) ≡ a * c + a * d + b * c + b * d
lemma-*over+ a b c d =
    begin
        (a + b) * (c + d)
    ≡⟨ lemma-*rdist (c + d) a b ⟩
        a * (c + d) + b * (c + d)
    ≡⟨ cong (λ x → x + b * (c + d)) (lemma-*ldist a c d) ⟩
        (a * c + a * d) + b * (c + d)
    ≡⟨ cong (λ x → a * c + a * d + x) (lemma-*ldist b c d) ⟩
        (a * c + a * d) + (b * c + b * d)
    ≡⟨ sym (lemma-+assoc (a * c + a * d) (b * c) (b * d)) ⟩
        a * c + a * d + b * c + b * d
    ∎

even : ∀ n → Set
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

even+even≡even : ∀ n m → even n → even m → even (n + m)
even+even≡even zero m h₁ h₂ = h₂
even+even≡even (suc zero) zero h₁ h₂ = h₁
even+even≡even (suc zero) (suc zero) h₁ h₂ = tt
even+even≡even (suc zero) (suc (suc m)) h₁ h₂ =
    even+even≡even (suc zero) m h₁ h₂
even+even≡even (suc (suc n)) zero h₁ h₂ =
    even+even≡even n zero h₁ tt
even+even≡even (suc (suc n)) (suc zero) h₁ h₂ =
    even+even≡even n (suc zero) h₁ h₂
even+even≡even (suc (suc n)) (suc (suc m)) h₁ h₂ =
    even+even≡even n (suc (suc m)) h₁ h₂

odd+odd≡even : ∀ n m → ¬ (even n) → ¬ (even m) → even (n + m)
odd+odd≡even zero zero h₁ h₂ = tt
odd+odd≡even zero (suc zero) h₁ h₂ = h₂ (h₁ tt)
odd+odd≡even zero (suc (suc m)) h₁ h₂ =
    odd+odd≡even zero m (λ _ → h₁ tt) h₂
odd+odd≡even (suc zero) zero h₁ h₂ = h₂ tt
odd+odd≡even (suc zero) (suc zero) h₁ h₂ = tt
odd+odd≡even (suc zero) (suc (suc m)) h₁ h₂ =
    odd+odd≡even (suc zero) m (λ z → z) h₂
odd+odd≡even (suc (suc n)) zero h₁ h₂ =
    odd+odd≡even n zero (λ _ → h₂ tt) (λ _ → h₂ tt)
odd+odd≡even (suc (suc n)) (suc zero) h₁ h₂ =
    odd+odd≡even n (suc zero) (λ z → h₂ (h₁ z)) (λ z → z)
odd+odd≡even (suc (suc n)) (suc (suc m)) h₁ h₂ =
    odd+odd≡even n (suc (suc m)) h₁ h₂

even+odd≡odd : ∀ n m → even n → ¬ (even m) → ¬ (even (n + m))
even+odd≡odd zero zero h₁ h₂ = λ _ → h₂ tt
even+odd≡odd zero (suc zero) h₁ h₂ = λ z → z
even+odd≡odd zero (suc (suc m)) h₁ h₂ = h₂
even+odd≡odd (suc zero) zero h₁ h₂ = λ z → z
even+odd≡odd (suc zero) (suc zero) h₁ h₂ = λ _ → h₂ h₁
even+odd≡odd (suc zero) (suc (suc m)) h₁ h₂ = λ _ → h₁
even+odd≡odd (suc (suc n)) zero h₁ h₂ = λ _ → h₂ tt
even+odd≡odd (suc (suc n)) (suc zero) h₁ h₂ =
    even+odd≡odd n (suc zero) h₁ (λ z → z)
even+odd≡odd (suc (suc n)) (suc (suc m)) h₁ h₂ =
    even+odd≡odd n (suc (suc m)) h₁ h₂

even-sucsuc : ∀ n → even (suc (suc n)) → even n
even-sucsuc n = λ z → z

sucsuc-even : ∀ n → even n → even (suc (suc n))
sucsuc-even n = λ x → x

lemma-++ : ∀ n → n + suc (suc n) ≡ suc (suc (n + n))
lemma-++ n =
    begin
        n + suc (suc n)
    ≡⟨ sym (lemma-+sucgr n (suc n)) ⟩
        suc (n + suc n)
    ≡⟨ cong suc (sym (lemma-+sucgr n n)) ⟩
        suc (suc (n + n))
    ∎

even-++ : ∀ n → even (n + n)
even-++ zero = tt
even-++ (suc zero) = tt
even-++ (suc (suc n)) = subst even (sym (lemma-++ n)) (even-++ n)

even*n≡even : ∀ n m → even n → even (n * m)
even*n≡even zero m h = tt
even*n≡even (suc zero) _ ()
even*n≡even (suc (suc n)) m h =
    subst even (lemma-+assoc m m (n * m))
               (even+even≡even (m + m) (n * m) (even-++ m) (even*n≡even n m h))

odd : ∀ n → even (suc n) → ¬ (even n)
odd zero h = λ _ → h
odd (suc zero) h = λ z → z
odd (suc (suc n)) h = odd n h

even-plus-assoc : ∀ n m → even ((m + m) + (n * m)) → even (m + (m + n * m))
even-plus-assoc n m = subst even (lemma-+assoc m m (n * m))

lemma-uncong-suc : ∀ n m → suc n ≡ suc m → n ≡ m
lemma-uncong-suc .m m refl = refl

lemma-+drop : ∀ n m o → o + n ≡ o + m → n ≡ m
lemma-+drop n m zero h = h
lemma-+drop n m (suc o) h =
    lemma-+drop n m o (lemma-uncong-suc (o + n) (o + m) h)

lemma-*drop : ∀ n m o → n ≡ m → n * o ≡ m * o
lemma-*drop zero zero o h = refl
lemma-*drop zero (suc m) o ()
lemma-*drop (suc n) zero o ()
lemma-*drop (suc n) (suc m) o h = cong (λ x → x * o) h

even-plus : ∀ n m → even (n + m) → even n → even m
even-plus zero m h₁ h₂ = h₁
even-plus (suc n) zero h₁ h₂ = tt
even-plus (suc zero) (suc zero) h₁ h₂ = h₂
even-plus (suc zero) (suc (suc m)) h₁ h₂ = even-plus (suc zero) m h₁ h₂
even-plus (suc (suc n)) (suc zero) h₁ h₂ = even-plus n (suc zero) h₁ h₂
even-plus (suc (suc n)) (suc (suc m)) h₁ h₂ = even-plus n (suc (suc m)) h₁ h₂

even-sucsuc* : ∀ n m → even (suc (suc n) * m) → even (n * m)
even-sucsuc* n m h = even-plus (2 * m) (n * m)
    (subst even (lemma-*rdist m (suc (suc zero)) n) h)
    (subst even (lemma-+assoc m m zero)
        (subst even (sym (lemma-+0 (m + m))) (even-++ m)))

odd*odd≡odd : ∀ n m → ¬ (even n) → ¬ (even m) → ¬ (even (n * m))
odd*odd≡odd zero m h₁ h₂ = λ _ → h₁ tt
odd*odd≡odd (suc zero) m h₁ h₂ = λ x → h₂ (subst even (lemma-+0 m) x)
odd*odd≡odd (suc (suc n)) m h₁ h₂ =
    λ x → odd*odd≡odd n m h₁ h₂ (even-sucsuc* n m x)

data Even : ℕ → Set where
    even-0  : Even 0
    even-2+ : {n : ℕ} → Even n → Even (suc (suc n))

EvenDecidable : Set
EvenDecidable = ∀ n → Dec (Even n)

even' : EvenDecidable
even' zero = yes even-0
even' (suc zero) = no (λ ())
even' (suc (suc n)) with even' n
even' (suc (suc n)) | yes p = yes (even-2+ p)
even' (suc (suc n)) | no p = no (λ { (even-2+ x) → p x} )

even+even≡even' : ∀ n m → Even n → Even m → Even (n + m)
even+even≡even' .0 m even-0 h₂ = h₂
even+even≡even' .(suc (suc n)) m (even-2+ {n} h₁) h₂ =
    even-2+ (even+even≡even' n m h₁ h₂)

even-sucsuc' : ∀ n → Even (suc (suc n)) → Even n
even-sucsuc' n (even-2+ h) = h

even-++' : ∀ n → Even (n + n)
even-++' zero = even-0
even-++' (suc zero) = even-2+ even-0
even-++' (suc (suc n)) =
    subst Even (cong suc (cong suc (sym (lemma-++ n))))
        (even-2+ (even-2+ (even-++' n)))

even*n≡even' : ∀ n m → Even n → Even (n * m)
even*n≡even' .0 m even-0 = even-0
even*n≡even' .(suc (suc n)) m (even-2+ {n} h) =
    subst Even (lemma-+assoc m m (n * m))
               (even+even≡even' (m + m) (n * m) (even-++' m)
                                (even*n≡even' n m h))

odd*odd≡both-odd : ∀ n m → ¬ (Even (n * m)) → ¬ (Even n) × ¬ (Even m)
odd*odd≡both-odd n m h =
    (λ x → h (even*n≡even' n m x)) ,
    (λ x → h (subst Even (lemma-*comm m n) (even*n≡even' m n x)))

n+sucn-odd : ∀ n → ¬ (even (n + suc n))
n+sucn-odd zero = λ z → z
n+sucn-odd (suc zero) = λ z → z
n+sucn-odd (suc (suc n)) =
    λ x → n+sucn-odd n
        (even-sucsuc (n + (suc n))
                     (subst even (sym (lemma-+sucgr (suc n) (suc n)))
                            (subst even (sym (lemma-+sucgr n (suc (suc n)))) x)))
