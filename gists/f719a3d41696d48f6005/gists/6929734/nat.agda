even*n≡even : ∀ n m → even n → even (n * m)
even*n≡even zero m h = tt
even*n≡even (suc zero) zero h = tt
even*n≡even (suc zero) (suc zero) h = h
even*n≡even (suc zero) (suc (suc m)) h = even*n≡even (suc zero) m h
even*n≡even (suc (suc n)) zero h = even*n≡even n zero h
even*n≡even (suc (suc n)) (suc zero) h = even*n≡even n (suc zero) h
even*n≡even (suc (suc n)) (suc (suc m)) h = {!!}
