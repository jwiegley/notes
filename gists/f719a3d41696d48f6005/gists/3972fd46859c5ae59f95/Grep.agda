filterMaybeIx : {A : Set} {P : A → Set}
              → (∀ x → Maybe (P x)) → (xs : List A)
              → List (Result A xs P)
filterMaybeIx p [] = []
filterMaybeIx p (x ∷ xs) = go x (p x) (suc′ <$> filterMaybeIx p xs)
  where
    go : ∀ {A : Set} {P : A → Set} {xs : List A}
       → (x : A)
       → Maybe (P x)
       → List (Result A xs P)
       → List (Result A xs P)
    go x nothing rest  = rest
    go x (just y) rest = (x , zero refl , y) ∷ rest
