module nat where

record ⊤ : Set where
data ⊥ : Set where

tt : ⊤
tt = record {}

-- ≡ is \==
infix 4 _≡_
data _≡_ {A : Set} (n : A) : A → Set where
     refl : n ≡ n

 -- _≡_ is symmetric
sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- transitive
trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- A fun way to write transitivity
infixr 5 _~_
_~_ = trans

-- and congruent
cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong f refl = refl

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

lemma-succ= : ∀ a b → succ a ≡ succ b → a ≡ b
lemma-succ= x .x refl = refl

_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ n + m = succ (n + m)

lemma-+0 : ∀ n → n + zero ≡ n
lemma-+0 zero = refl
lemma-+0 (succ n) = cong succ (lemma-+0 n)

lemma-0+ : ∀ n → zero + n ≡ n
lemma-0+ zero = refl
lemma-0+ (succ n) = refl

lemma-+1 : ∀ n → n + succ zero ≡ succ n
lemma-+1 zero = refl
lemma-+1 (succ n) = cong succ (lemma-+1 n)

lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
lemma-+succ zero b = refl
lemma-+succ (succ a) b = cong succ (lemma-+succ a b)

lemma-+succgl : ∀ a b → succ (a + b) ≡ succ a + b
lemma-+succgl zero b = refl
lemma-+succgl (succ a) b = refl

lemma-+succgr : ∀ a b → succ (a + b) ≡ a + succ b
lemma-+succgr zero b = refl
lemma-+succgr (succ a) b = cong succ (lemma-+succgr a b)

lemma-+succ2 : ∀ a b → succ a + succ b ≡ a + succ (succ b)
lemma-+succ2 zero b = refl
lemma-+succ2 (succ a) b = cong succ (lemma-+succ a (succ b))

lemma-+comm : ∀ n m → n + m ≡ m + n
lemma-+comm zero zero = refl
lemma-+comm zero (succ m) = cong succ (sym (lemma-+0 m))
lemma-+comm (succ n) m = cong succ (lemma-+comm n m) ~ lemma-+succ m n

lemma-+assoc : ∀ n m o → n + (m + o) ≡ (n + m) + o
lemma-+assoc zero m o = refl
lemma-+assoc (succ n) m o = cong succ (lemma-+assoc n m o)

lemma-+shuffle : ∀ n m o → n + (m + o) ≡ m + (n + o)
lemma-+shuffle zero m o = refl
lemma-+shuffle (succ n) m o =
    cong succ (lemma-+shuffle n m o) ~ (lemma-+succgr m (n + o))

lemma-+distrib : ∀ n m o p → (n + m) + (o + p) ≡ (n + o) + (m + p)
lemma-+distrib zero m o p = lemma-+shuffle m o p
lemma-+distrib (succ n) m o p = cong succ (lemma-+distrib n m o p)

_*_ : ℕ → ℕ → ℕ
zero   * _ = zero
succ n * m = m + (n * m)

lemma-*+ : ∀ n → succ zero * n ≡ n
lemma-*+ = lemma-+0

lemma-*succ : ∀ n m → succ n * m ≡ m + (n * m)
lemma-*succ n m = refl
