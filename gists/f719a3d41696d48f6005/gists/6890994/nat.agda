lemma-*rdist : ∀ n m o → (m + o) * n ≡ m * n + o * n
lemma-*rdist zero m o =
    begin
        (m + o) * 0
    ≡⟨ lemma-*0 (m + o) ⟩
        zero
    ≡⟨ sym (lemma-+*0 m o) ⟩
        m * 0 + o * 0
    ∎
lemma-*rdist (suc n) m o =
    begin
        (m + o) * suc n
    ≡⟨ lemma-*suc (m + o) n ⟩
        m + o + (m + o) * n
    ≡⟨ cong (_+_ (m + o)) (lemma-*rdist n m o) ⟩
        m + o + (m * n + o * n)
    ≡⟨ lemma-+distrib m o (m * n) (o * n) ⟩
        (m + m * n) + (o + o * n)
    ≡⟨ sym (cong (_+_ (m + m * n)) (lemma-*suc o n)) ⟩
        (m + m * n) + o * suc n
    ≡⟨ lemma-+comm (m + m * n) (o * suc n) ⟩
        o * suc n + (m + m * n)
    ≡⟨ sym (cong (_+_ (o * suc n)) (lemma-*suc m n)) ⟩
        o * suc n + m * suc n
    ≡⟨ lemma-+comm (o * suc n) (m * suc n) ⟩
        m * suc n + o * suc n
    ∎
