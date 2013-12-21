module st where

open import Data.Nat hiding (_⊔_; suc; zero)
open import Data.Sum
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data ⊥ : Set where
record ⊤ : Set where

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Pred A ℓ = A → Set ℓ

module _ {a} {A : Set a} where
    infix 4 _∈_ _∉_

    -- Membership: Axiom of specification.

    _∈_ : ∀ {ℓ} → A → Pred A ℓ → Set _
    x ∈ P = P x

    _∉_ : ∀ {ℓ} → A → Pred A ℓ → Set _
    x ∉ P = ¬ x ∈ P

    -- Equality: Axiom of extensionality.

    _==_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    P == Q = ∀ {x} → x ∈ P → x ∈ Q → x ∉ P → x ∉ Q

    -- singleton : ∀ {ℓ} → A → Pred A ℓ
    -- singleton x = λ y → x ≈ y

    _pair_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    P pair Q = ∀ x → P x → Q x

    -- The empty set.

    ∅ : Pred A _
    ∅ = λ _ → ⊥

    -- The property of being empty.

    Empty : ∀ {ℓ} → Pred A ℓ → Set _
    Empty P = ∀ x → x ∉ P

    ∅-Empty : Empty ∅
    ∅-Empty x ()

    -- The property of inclusion.

    infix 4 _⊆_ _⊇_ _⊂_ _⊃_

    _⊆_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

    _⊇_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    Q ⊇ P = P ⊆ Q

    _⊂_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    P ⊂ Q = ∀ {x y} → x ∈ P → x ∈ Q → y ∉ P → y ∈ Q

    _⊃_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
    Q ⊃ P = P ⊂ Q

    -- Axiom of unions.

    _∪_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
    Q ∪ P = λ x → Q x ⊎ P x

x⊎⊥≡x : ∀ {a} {x : Set a} → x ⊎ ⊥ → x
x⊎⊥≡x (inj₁ x) = x
x⊎⊥≡x (inj₂ ())

P∪∅≡P : ∀ {ℓ a} {A : Set a} (P : Pred A ℓ) → P ∪ ∅ ≡ P
P∪∅≡P p =
    begin
        p ∪ ∅
    ≡⟨ refl ⟩
        (λ x → p x ⊎ ⊥)
    ≡⟨ cong x⊎⊥≡x refl ⟩
        (λ x → p x)
    ≡⟨ refl ⟩
        p
    ∎

⊆-trans : ∀ {ℓ₁ ℓ₂ ℓ₃ a} {A : Set a}
          {P : Pred A ℓ₁} {Q : Pred A ℓ₂} {R : Pred A ℓ₃}
          → P ⊆ Q → Q ⊆ R → P ⊆ R
⊆-trans h₁ h₂ = λ x₁ → h₂ (h₁ x₁)

nats : Pred ℕ zero
nats = λ (x : ℕ) → ⊤
