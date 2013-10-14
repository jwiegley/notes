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
