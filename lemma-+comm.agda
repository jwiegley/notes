lemma-+comm : (n m : ℕ) → n + m ≡ m + n
lemma-+comm zero zero = refl
lemma-+comm zero (succ m) = cong succ (sym (lemma-+0 m))
-- lemma-+comm (succ n) m = cong succ (lemma-+comm n m) ~ lemma-+succ m n
lemma-+comm (succ n) zero = cong succ (lemma-+0 n)
lemma-+comm (succ n) (succ m) = {!!}
