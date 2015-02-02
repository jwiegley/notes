private
  suc′ : ∀ {A} {P : A → Set} {x : A} {xs : List A} →
         Σ A (λ x₁ → Σ (Any (_≡_ x₁) xs) (λ _ → P x₁)) →
         Σ A (λ x₁ → Σ (Any (_≡_ x₁) (x ∷ xs)) (λ _ → P x₁))
  suc′ (x , p , y) = x , suc p , y

Result : ∀ A xs (P : A → Set) → Set
Result A xs P = Σ A (λ x → x ∈ xs × P x)

filterMaybeIx : {A : Set} {P : A → Set}
              → (∀ x → Maybe (P x)) → (xs : List A)
              → List (Result A xs P)
filterMaybeIx p [] = []
filterMaybeIx p (x ∷ xs) with (p x)
filterMaybeIx p (x ∷ xs) | nothing = rest
  where rest = suc′ <$> filterMaybeIx p xs
filterMaybeIx p (x ∷ xs) | just x₁ = (x , zero refl , x₁) ∷ rest
  where rest = suc′ <$> filterMaybeIx p xs
