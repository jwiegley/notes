even : ∀ n → Set
even zero = ⊤
even (suc zero) = ⊥
even (suc (suc n)) = even n

even+even≡even : ∀ n m → even n → even m → even (n + m)
even+even≡even zero m h₁ h₂ = h₂
even+even≡even (suc n) m h₁ h₂ = {!!}
