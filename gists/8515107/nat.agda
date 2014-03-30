n+sucn-odd : ∀ n → ¬ (even (n + suc n))
n+sucn-odd zero = λ z → z
n+sucn-odd (suc zero) = λ z → z
n+sucn-odd (suc (suc n)) = 
    λ x → n+sucn-odd n
        (even-sucsuc (n + (suc n))
                     (subst even (sym (lemma-+sucgr (suc n) (suc n)))
                            (subst even (sym (lemma-+sucgr n (suc (suc n)))) x)))
