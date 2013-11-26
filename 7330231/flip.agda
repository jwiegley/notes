module flip where

open import Function hiding (_∘_; flip)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

flip : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
flip f b a = f a b

_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

flip-distrib : ∀ {A B C : Set} (f : A → B) (g : B → B → C)
               → flip ((λ x → x ∘ f) ∘ g) ≡ flip g ∘ f
flip-distrib f g = refl
