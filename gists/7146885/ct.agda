data _-Nat⟶_ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    {C : Category c₁ c₂ ℓ}
    {D : Category c₁′ c₂′ ℓ′}
    (A B : Functor C D) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    NatTrans : ((x : Category.Obj C)
                → Category.Hom D (Functor.FObj A x) (Functor.FObj B x))
             → _-Nat⟶_ A B
