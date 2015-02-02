    fun-compose′ : ∀ {E A B C : Set}  {M : Set → Set} {m-dict : Monad M}
                   (f : A → B) (g : B → C) (x : EitherT E M A)
               → fmap′ (g ∘ f) x ≡ fmap′ g (fmap′ f x)
    fun-compose′ {m-dict = m-dict} f g (mkEitherT x) =
        begin
            fmap′ (g ∘ f) (mkEitherT x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (fmap {{EitherF}} (g ∘ f)) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (λ y → fmap {{EitherF}} g (fmap {{EitherF}} f y)) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (fmap {{EitherF}} g ∘ fmap {{EitherF}} f) x)
        ≡⟨ refl ⟩
            mkEitherT (fmap (fmap {{EitherF}} g) (fmap (fmap {{EitherF}} f) x))
        ≡⟨ refl ⟩
            fmap′ g (fmap′ f (mkEitherT x))
        ∎
