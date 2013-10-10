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
even+even≡even (suc (suc n)) m h₁ h₂ = even+even≡even n m h₁ h₂
