data _≤≤_ : ℕ → ℕ → Set where

  n≤≤n : ∀ {n : ℕ}
      --------
    → n ≤≤ n

  n≤≤s : ∀ {m n : ℕ}
    → m ≤≤ n
      -------------
    → m ≤≤ suc n

n≤n : ∀ (n : ℕ) → n ≤ n
n≤n zero = z≤n
n≤n (suc n) = s≤s (n≤n n)

0≤≤n : ∀ (n : ℕ) → 0 ≤≤ n
0≤≤n zero = n≤≤n
0≤≤n (suc n) = n≤≤s (0≤≤n n)

≤-suc : ∀ (m n : ℕ) → m ≤ n → m ≤ suc n
≤-suc .0 n z≤n = z≤n
≤-suc (suc m) (suc n) (s≤s H) = s≤s (≤-suc m n H)

≤≤-suc : ∀ (m n : ℕ) → m ≤≤ n → suc m ≤≤ suc n
≤≤-suc m .m n≤≤n = n≤≤n
≤≤-suc m (suc n) (n≤≤s H) = n≤≤s (≤≤-suc m n H)

≤≤-to-≤ : ∀ (m n : ℕ) → m ≤≤ n → m ≤ n
≤≤-to-≤ m m n≤≤n = n≤n m
≤≤-to-≤ m (suc n) (n≤≤s H) = ≤-suc m n (≤≤-to-≤ m n H)

≤-to-≤≤ : ∀ (m n : ℕ) → m ≤ n → m ≤≤ n
≤-to-≤≤ .0 n z≤n = 0≤≤n n
≤-to-≤≤ (suc m) (suc n) (s≤s H) = ≤≤-suc m n (≤-to-≤≤ m n H)
