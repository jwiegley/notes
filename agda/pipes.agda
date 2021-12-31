module pipes where

-- open import container.m.core

data Pipe (a b r : Set) : Set where
  pure : r → Pipe a b r
  await : (a → Pipe a b r) → Pipe a b r
  yield : b → ∞ (Pipe a b r) → Pipe a b r

data _≈_ {a b r : Set} : Pipe a b r → Pipe a b r → Set where
  pure-≈ : {x : r} → pure x ≈ pure x
  await-≈ : {k₁ k₂ : a → Pipe a b r}
          → ((x : a) → (k₁ x ≈ k₂ x))
          → await k₁ ≈ await k₂
  yield-≈ : {x : b}{p₁ p₂ : ∞ (Pipe a b r)}
          → ∞ ((♭ p₁) ≈ (♭ p₂))
          → yield x p₁ ≈ yield x p₂
infix 4 _≈_

refl-≈ : ∀ {a b r}{p : Pipe a b r} → p ≈ p
refl-≈ {p = pure x} = pure-≈
refl-≈ {p = await k} = await-≈ (λ _ → refl-≈)
refl-≈ {p = yield x p} = yield-≈ (♯ refl-≈)

-- Pipe is a functor
map : ∀ {a b r s} → (r → s) → Pipe a b r → Pipe a b s
map f (pure x) = pure (f x)
map f (await k) = await (λ x → map f (k x))
map f (yield b p) = yield b (♯ map f (♭ p))

-- Pipe is a monad
return : ∀ {a b r} → r → Pipe a b r
return = pure

join : ∀ {a b r} → Pipe a b (Pipe a b r) → Pipe a b r
join (pure p) = p
join (await k) = await (λ x → join (k x))
join (yield b p) = yield b (♯ join (♭ p))

-- monad laws
runit : ∀ {a b r}(p : Pipe a b r)
      → join (return p) ≈ p
runit p = refl-≈

lunit : ∀ {a b r}(p : Pipe a b r)
      → join (map return p) ≈ p
lunit (pure x) = pure-≈
lunit (await k) = await-≈ (λ x → lunit (k x))
lunit (yield b p) = yield-≈ (♯ (lunit (♭ p)))

assoc : ∀ {a b r}(p : Pipe a b (Pipe a b (Pipe a b r)))
      → join (join p) ≈ join (map join p)
assoc (pure p) = refl-≈
assoc (await k) = await-≈ (λ x → assoc (k x))
assoc (yield x p) = yield-≈ (♯ (assoc (♭ p)))

-- Pipe is a category
cat : ∀ {a r} → Pipe a a r
cat = await (λ x → yield x (♯ cat))

_>+>_ : ∀ {a b c r} → Pipe a b r → Pipe b c r → Pipe a c r
p₁ >+> pure x = pure x
p₁ >+> yield x p₂ = yield x (♯ (p₁ >+> ♭ p₂))
pure x >+> p₂ = pure x
await k >+> p₂ = await (λ x → k x >+> p₂)
yield x p₁ >+> await k = ♭ p₁ >+> k x
infixl 5 _>+>_

-- category laws
>+>-lunit : ∀ {a b r}(p : Pipe a b r)
          → cat >+> p ≈ p
>+>-lunit (pure x) = refl-≈
>+>-lunit (await k) = await-≈ (λ x → >+>-lunit (k x))
>+>-lunit (yield x p) = yield-≈ (♯ >+>-lunit (♭ p))

>+>-runit : ∀ {a b r}(p : Pipe a b r)
          → p >+> cat ≈ p
>+>-runit (pure x) = refl-≈
>+>-runit (await k) = await-≈ (λ x → >+>-runit (k x))
>+>-runit (yield x p) = yield-≈ (♯ (>+>-runit (♭ p)))

>+>-assoc : ∀ {a b c d r}
          → (p₁ : Pipe a b r)
          → (p₂ : Pipe b c r)
          → (p₃ : Pipe c d r)
          → (p₁ >+> p₂) >+> p₃
          ≈ p₁ >+> (p₂ >+> p₃)
>+>-assoc p₁ p₂ (pure x) = refl-≈
>+>-assoc p₁ p₂ (yield x p₃) = yield-≈ (♯ >+>-assoc p₁ p₂ (♭ p₃))
>+>-assoc p₁ (pure x) (await k₃) = refl-≈
>+>-assoc p₁ (yield x p₂) (await k₃) = >+>-assoc p₁ (♭ p₂) (k₃ x)
>+>-assoc (pure x) (await k₂) (await k₃) = refl-≈
>+>-assoc (yield x p₁) (await k₂) (await k₃)
  = >+>-assoc (♭ p₁) (k₂ x) (await k₃)
>+>-assoc (await k₁) (await k₂) (await k₃)
  = await-≈ (λ x → >+>-assoc (k₁ x) (await k₂) (await k₃))
