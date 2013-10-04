lemma-+0 : (n : ℕ) → n + zero ≡ n
lemma-+0 zero = refl
lemma-+0 (succ n) = cong succ (lemma-+0 n)

lemma-0+ : (n : ℕ) → zero + n ≡ n
lemma-0+ zero = refl
lemma-0+ (succ n) = refl

lemma-+1 : (n : ℕ) → n + succ zero ≡ succ n
lemma-+1 zero = refl
lemma-+1 (succ n) = cong succ (lemma-+1 n)

lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
lemma-+succ zero b = refl
lemma-+succ (succ a) b = cong succ (lemma-+succ a b)

lemma-+succg : ∀ a b → succ (a + b) ≡ succ a + b
lemma-+succg zero b = refl
lemma-+succg (succ a) b = refl

lemma-=succ : ∀ a b → succ a ≡ succ b → a ≡ b
lemma-=succ x .x refl = refl

lemma-+comm : (n m : ℕ) → n + m ≡ m + n
lemma-+comm zero zero = refl
lemma-+comm zero (succ m) = cong succ (sym (lemma-+0 m))
-- lemma-+comm (succ n) m = cong succ (lemma-+comm n m) ~ lemma-+succ m n
lemma-+comm (succ n) zero = cong succ (lemma-+0 n)
lemma-+comm (succ n) (succ m) = {!!}
