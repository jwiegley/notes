lemma-+sucgr : ∀ a b → suc (a + b) ≡ a + suc b
lemma-+sucgr zero b = refl
lemma-+sucgr (suc a) b = cong suc (lemma-+sucgr a b)
