even*n≡even : ∀ n m → even n → even (n * m)
even*n≡even zero m h = tt
even*n≡even (suc zero) _ ()
even*n≡even (suc (suc n)) m h =
    subst even (lemma-+assoc m m (n * m))
               (even+even≡even (m + m) (n * m) (even-++ m) (even*n≡even n m h))
