module Conduit where

open import Lists

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

sym : ∀ {A : Set} (x y : A) → x ≡ y → y ≡ x
sym x .x refl = refl

trans : ∀ {A : Set} (x y z : A) → x ≡ y → y ≡ z → x ≡ z
trans x .x .x refl refl = refl

subst : ∀ {A : Set} (x y : A) → x ≡ y → ∀ (P : A → Set) → P x → P y
subst x .x refl P Pa = Pa

cong : ∀ {A : Set} (x y : A) → (∀ (P : A → Set) → P x → P y) → x ≡ y
cong x y H = H (_≡_ x) refl

id : ∀ {A : Set} → A → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ f g x = f (g x)

const : ∀ {A B : Set} → B → A → B
const x _ = x

record IsFunctor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

    fun_ident : ∀ {A} {x : F A} → fmap id x ≡ id x
    fun_assoc : ∀ {A B C} (f : A → B) (g : B → C) (x : F A)
              → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x

record Functor (F : Set → Set) : Set₁ where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
    isFunctor : IsFunctor F

  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

record IsApplicative (F : Set → Set) : Set₁ where
  field
    pure  : ∀ {A} → A → F A
    apply : ∀ {A B} → F (A → B) → F A → F B

    app_ident : ∀ {A} {x : F A} → apply (pure id) x ≡ id x
    app_composition : ∀ {X Y Z} (v : F (X → Y)) (u : F (Y → Z)) (w : F X) →
        apply (apply (apply (pure _∘_) u) v) w ≡ apply u (apply v w)
    app_homomorphism : ∀ {X Y} (x : X) (f : X → Y) →
        apply (pure f) (pure x) ≡ pure (f x)
    app_interchange : ∀ {X Y} (y : X) (u : F (X → Y)) →
        apply u (pure y) ≡ apply (pure (λ f → f y)) u

    app_fmap_unit : ∀ {fun_dict : Functor F} {X Y : Set}
                      (f : X → Y) (x : F X) →
        apply (pure f) x ≡ fmap f x

record Applicative (F : Set → Set) : Set₁ where
  infixl 4 _<*>_
  field
    functor : Functor F
    pure : ∀ {A} → A → F A
    apply : ∀ {A B} → F (A → B) → F A → F B
    isApplicative : IsApplicative F

  _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  _<*>_ = apply

open Applicative {{...}} public

-- record IsMonad (F : Set → Set)
--     (fmap : ∀ {A B} → (A → B) → F A → F B) : Set₁ where
--   field
--     fun_ident : ∀ {A} {x : F A} → fmap id x ≡ id x
--     fun_assoc : ∀ {A B C} {f : A → B} {g : B → C} {x : F A}
--             → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x

-- record Monad : Set₁ where
--   field
--     F : Set → Set
--     fmap : ∀ {A B} → (A → B) → F A → F B
--     isMonad : IsMonad F fmap

-- open Monad {{...}} public

IdentityF : Functor (λ x → x)
IdentityF = record
    { fmap = λ f x → f x
    ; isFunctor = record
        { fmap      = λ f x → f x

        ; fun_ident = λ {A} → refl
        ; fun_assoc = λ {A} _ _ _ → refl
        }
    }

IdentityA : Applicative (λ x → x)
IdentityA = record
    { functor = IdentityF
    ; pure    = id
    ; apply   = λ f x → f x
    ; isApplicative = record
        { pure  = id
        ; apply = λ f x → f x

        ; app_ident        = λ {A} {x} → refl
        ; app_composition  = λ {X} {Y} {Z} v u w → refl
        ; app_homomorphism = λ {X} {Y} x f → refl
        ; app_interchange  = λ {X} {Y} y u → refl

        ; app_fmap_unit    = app_fmap_unit_
        }
    }
  where
    app_fmap_unit_ : ∀ {fun_dict X Y} (f : X → Y) (x : X)
                   → f x ≡ Functor.fmap fun_dict f x
    app_fmap_unit_ {fun_dict = dict} f x = {!!}

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just    : ∀ (a : A) → Maybe A

MaybeF : Functor Maybe
MaybeF = record
    { fmap = fmap_
    ; isFunctor = record
        { fmap = fmap_

        ; fun_ident = ident_
        ; fun_assoc = assoc_
        }
    }
  where
    fmap_ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
    fmap_ f Nothing = Nothing
    fmap_ f (Just a) = Just (f a)

    ident_ : ∀ {A : Set} {x : Maybe A} → fmap_ id x ≡ id x
    ident_ {x = Nothing} = refl
    ident_ {x = Just _}  = refl

    assoc_ : ∀ {A B C : Set} (f : A → B) (g : B → C) (x : Maybe A) →
         (fmap_ (λ x₁ → g (f x₁))) x ≡ (fmap_ g) ((fmap_ f) x)
    assoc_ _ _ Nothing  = refl
    assoc_ _ _ (Just _) = refl

data Either (E A : Set) : Set where
  Left  : ∀ (e : E) → Either E A
  Right : ∀ (a : A) → Either E A

EitherF : ∀ {E : Set} → Functor (Either E)
EitherF = record
    { fmap = fmap_
    ; isFunctor = record
        { fmap = fmap_

        ; fun_ident = ident_
        ; fun_assoc = assoc_
        }
    }
  where
    fmap_ : ∀ {E A B : Set} → (A → B) → Either E A → Either E B
    fmap_ f (Left e)  = Left e
    fmap_ f (Right a) = Right (f a)

    ident_ : ∀ {E A : Set} {x : Either E A} → fmap_ id x ≡ id x
    ident_ {x = Left _}  = refl
    ident_ {x = Right _} = refl

    assoc_ : ∀ {E A B C : Set} (f : A → B) (g : B → C) (x : Either E A) →
         (fmap_ (λ x₁ → g (f x₁))) x ≡ (fmap_ g) ((fmap_ f) x)
    assoc_ _ _ (Left _)  = refl
    assoc_ _ _ (Right _) = refl
