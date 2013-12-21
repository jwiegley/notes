even : ∀ n → Set
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

even+even≡even : ∀ n m → even n → even m → even (n + m)
even+even≡even zero m h₁ h₂ = h₂
even+even≡even (suc zero) zero () h₂
even+even≡even (suc zero) (suc zero) () ()
even+even≡even (suc zero) (suc (suc m)) h₁ h₂ =
    even+even≡even (suc zero) m h₁ h₂
even+even≡even (suc (suc n)) m h₁ h₂ = even+even≡even n m h₁ h₂

odd+odd≡even : ∀ n m → ¬ (even n) → ¬ (even m) → even (n + m)
odd+odd≡even zero zero h₁ h₂ = tt
odd+odd≡even zero (suc zero) h₁ h₂ = h₂ (h₁ tt)
odd+odd≡even zero (suc (suc m)) h₁ h₂ = odd+odd≡even zero m (λ _ → h₁ tt) h₂
odd+odd≡even (suc zero) zero h₁ h₂ = h₂ tt
odd+odd≡even (suc zero) (suc zero) h₁ h₂ = tt
odd+odd≡even (suc zero) (suc (suc m)) h₁ h₂ =
    odd+odd≡even (suc zero) m (λ z → z) h₂
odd+odd≡even (suc (suc n)) m h₁ h₂ = odd+odd≡even n m h₁ h₂

even+odd≡odd : ∀ n m → even n → ¬ (even m) → ¬ (even (n + m))
even+odd≡odd zero m h₁ h₂ = h₂
even+odd≡odd (suc zero) m h₁ h₂ = λ _ → h₁
even+odd≡odd (suc (suc n)) m h₁ h₂ = even+odd≡odd n m h₁ h₂

even*n≡even : ∀ n m → even n → even (n * m)
even*n≡even zero _ _ = tt
even*n≡even (suc zero) zero _ = tt
even*n≡even (suc zero) (suc zero) h = h
even*n≡even (suc zero) (suc (suc m)) h = even*n≡even (suc zero) m h
even*n≡even (suc (suc n)) m h = {!!}

odd*odd≡odd : ∀ n m → ¬ (even n) → ¬ (even m) → ¬ (even (n * m))
odd*odd≡odd zero m h₁ h₂ = λ _ → h₁ tt
odd*odd≡odd (suc zero) zero h₁ h₂ = λ _ → h₂ tt
odd*odd≡odd (suc zero) (suc zero) h₁ h₂ = λ z → z
odd*odd≡odd (suc zero) (suc (suc m)) h₁ h₂ =
    odd*odd≡odd (suc zero) m (λ z → z) h₂
odd*odd≡odd (suc (suc n)) zero h₁ h₂ = λ _ → h₂ tt
odd*odd≡odd (suc (suc n)) (suc zero) h₁ h₂ =
    odd*odd≡odd n (suc zero) (λ z → h₂ (h₁ z)) (λ z → z)
odd*odd≡odd (suc (suc n)) (suc (suc m)) h₁ h₂ = {!!}
