    fmap′ : ∀ {E A B : Set} {M : Set → Set} {m-dict : Monad M}
          → (A → B) → EitherT E M A → EitherT E M B
    fmap′ f (mkEitherT x) = mkEitherT (fmap (fmap {{EitherF}} f) x)

    fun-ident′ : ∀ {E A : Set} {M : Set → Set} {m-dict : Monad M}
                   (x : EitherT E M A) → fmap′ id x ≡ x
    fun-ident′ {m-dict = m-dict} (mkEitherT m) =
        cong mkEitherT (IsFunctor.fun-ident fun-laws m)
      where
        fun-laws = Functor.isFunctor (Monad.base-functor m-dict)

    fun-compose′ : ∀ {E A B C : Set}  {M : Set → Set} {m-dict : Monad M}
                   (f : A → B) (g : B → C) (x : EitherT E M A)
               → fmap′ (g ∘ f) x ≡ fmap′ g (fmap′ f x)
    fun-compose′ {m-dict = m-dict} f g x =
        begin
            fmap′ (g ∘ f) x
        ≡⟨ {!refl!} ⟩
            mkEitherT (fmap (fmap {{EitherF}} (g ∘ f)) (runEitherT x))
        ≡⟨ {!!} ⟩
            fmap′ g (fmap′ f x)
        ∎
      where
        base = Monad.base-functor m-dict
