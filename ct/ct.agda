module ct where

open import alg
open import Level
open import Function hiding (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record IsCategory {c₁ c₂ ℓ : Level}
    (Obj : Set c₁)
    (Hom : Obj → Obj → Set c₂)
    (_≈_ : {A B : Obj} → Rel (Hom A B) ℓ)
    (_∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C)
    (Id  : {A : Obj} → Hom A A)
    : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  field
    equivalence : {A B : Obj} → IsEquivalence {c₂} {ℓ} {Hom A B} _≈_
    identityL   : {A B : Obj} → {f : Hom A B} → (Id ∘ f) ≈ f
    identityR   : {A B : Obj} → {f : Hom A B} → (f ∘ Id) ≈ f
    ∘-resp-≈    : {A B C : Obj} {f g : Hom A B} {h i : Hom B C}
                  → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
    associative : {A B C D : Obj} {f : Hom C D}  {g : Hom B C} {h : Hom A B}
                  → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)

record Category c₁ c₂ ℓ : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  infix  4 _≈_
  infixr 9 _∘_
  field
    Obj : Set c₁
    Hom : Obj → Obj → Set c₂
    _≈_ : {A B : Obj} → Rel (Hom A B) ℓ
    _∘_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    Id  : {A : Obj} → Hom A A
    isCategory : IsCategory Obj Hom _≈_ _∘_ Id

  op : Category c₁ c₂ ℓ
  op = record
      { Obj = Obj
      ; Hom = flip Hom
      ; _≈_ = _≈_
      ; _∘_ = flip _∘_
      ; Id  = Id
      ; isCategory = opIsCategory
      }
    where
      opIsCategory : IsCategory {c₁} {c₂} {ℓ} Obj (flip Hom) _≈_ (flip _∘_) Id
      opIsCategory = record
          { equivalence = IsCategory.equivalence isCategory
          ; identityL   = IsCategory.identityR isCategory
          ; identityR   = IsCategory.identityL isCategory
          ; associative =
                (IsEquivalence.sym (IsCategory.equivalence isCategory))
                (IsCategory.associative isCategory)
          ; ∘-resp-≈ = flip (IsCategory.∘-resp-≈ isCategory)
          }

  dom : {A B : Obj} → Hom A B → Obj
  dom {A} _ = A

  cod : {A B : Obj} → Hom A B → Obj
  cod {B = B} _ = B

  homsetoid : {A B : Obj } → Setoid c₂ ℓ
  homsetoid {A} {B} = record
      { Carrier = Hom A B
      ; isEquivalence = IsCategory.equivalence isCategory
      }

Obj : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Set c₁
Obj C = Category.Obj C

Hom : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Obj C → Obj C → Set c₂
Hom C = Category.Hom C

_[_≈_] : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g

_[_∘_] : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {a b c : Obj C}
         → Hom C b c → Hom C a b → Hom C a c
C [ f ∘ g ] = Category._∘_ C f g

infix  4 _[_≈_]
infixr 9 _[_∘_]

Id : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → (A : Obj C) → Hom C A A
Id {C = C} A = Category.Id C {A}

record IsFunctor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    (C : Category c₁ c₂ ℓ)
    (D : Category c₁′ c₂′ ℓ′)
    (FObj : Obj C → Obj D)
    (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
    : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    ≈-cong   : {A B : Obj C} {f g : Hom C A B}
             → C [ f ≈ g ] → D [ FMap f ≈ FMap g ]
    identity : {A : Obj C}
             →  D [ (FMap {A} {A} (Id {_} {_} {_} {C} A)) ≈
                    (Id {_} {_} {_} {D} (FObj A)) ]
    distr    : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
             → D [ FMap (C [ g ∘ f ]) ≈ (D [ FMap g ∘ FMap f ] )]

record Functor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    (domain : Category c₁ c₂ ℓ)
    (codomain : Category c₁′ c₂′ ℓ′)
    : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    FObj : Obj domain → Obj codomain
    FMap : {A B : Obj domain} → Hom domain A B
           → Hom codomain (FObj A) (FObj B)
    isFunctor : IsFunctor domain codomain FObj FMap

_⟶_ : ∀ {ℓ} (A B : Set ℓ) → Set _
x ⟶ y = x → y

_∘_ : ∀ {ℓ} {A B C : Set ℓ} (f : B → C) → (g : A → B) → (x : A) → C
f ∘ g = λ x → f (g x)

∘-resp-≈ : ∀ {ℓ} {A B C : Set ℓ} {f g : A → B} {h i : B → C}
         → f ≡ g → h ≡ i → h ∘ f ≡ i ∘ g
∘-resp-≈ refl refl = refl

Sets : {ℓ : Level} → Category _ _ ℓ
Sets {ℓ} = record
    { Obj = Set ℓ
    ; Hom = _⟶_
    ; _≈_ = _≡_
    ; _∘_ = _∘_
    ; Id  = id
    ; isCategory = setsIsCategory
    }
  where
    setsIsCategory : {ℓ : Level} → IsCategory (Set ℓ) _⟶_ _≡_ _∘_ id
    setsIsCategory = record
        { equivalence = record { refl = refl; sym = sym; trans = trans }
        ; identityL   = refl
        ; identityR   = refl
        ; associative = refl
        ; ∘-resp-≈    = ∘-resp-≈
        }

Identity : {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) → Functor C C
Identity C = record
    { FObj = id
    ; FMap = id
    ; isFunctor = record
        { ≈-cong = id
        ; identity = IsEquivalence.refl
            (IsCategory.equivalence (Category.isCategory C))
        ; distr = IsEquivalence.refl
            (IsCategory.equivalence (Category.isCategory C))
        }
    }

data _-Nat⟶_ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    {C : Category c₁ c₂ ℓ}
    {D : Category c₁′ c₂′ ℓ′}
    (A B : Functor C D) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    NatTrans : ((x : Category.Obj C)
                → Category.Hom D (Functor.FObj A x) (Functor.FObj B x))
             → A -Nat⟶ B

_-Nat≈_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
            {C : Category c₁ c₂ ℓ}
            {D : Category c₁′ c₂′ ℓ′}
            {F G : Functor C D} → F -Nat⟶ G → F -Nat⟶ G → Set c₁′
F -Nat≈ G = {!!}

_-Nat∘_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
            {C : Category c₁ c₂ ℓ}
            {D : Category c₁′ c₂′ ℓ′}
            {A B C : Functor C D}
            (f : B -Nat⟶ C) (g : A -Nat⟶ B) → (A -Nat⟶ C)
f -Nat∘ g = NatTrans (λ x → {!!})

IdNat : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    {C : Category c₁ c₂ ℓ}
    {D : Category c₁′ c₂′ ℓ′}
    (A : Functor C D) → A -Nat⟶ A
IdNat {C = C} F = NatTrans (λ x → Functor.FMap F (Category.Id C))

Fun : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
    → (C : Category c₁ c₂ ℓ)
    → (D : Category c₁′ c₂′ ℓ′)
    → Category _ _ c₁′
Fun {c₁} {c₂} {ℓ} {c₁′} {c₂′} {ℓ′} C D = record
    { Obj = Functor C D
    ; Hom = _-Nat⟶_
    ; _≈_ = _-Nat≈_
    ; _∘_ = _-Nat∘_
    ; Id  = λ {A} → IdNat A
    ; isCategory = funIsCategory
    }
  where
    funIsCategory : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
                    {C : Category c₁ c₂ ℓ}
                    {D : Category c₁′ c₂′ ℓ′}
                  → IsCategory (Functor C D)
                        _-Nat⟶_ _-Nat≈_ _-Nat∘_ (λ {A} → IdNat A)
    funIsCategory = record
        { equivalence =
              record { refl  = {!!}
                     ; sym   = {!!}
                     ; trans = {!!}
                     }
        ; identityL   = {!!}
        ; identityR   = {!!}
        ; associative = {!!}
        ; ∘-resp-≈    = {!!}
        }
