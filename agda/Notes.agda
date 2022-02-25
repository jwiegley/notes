module Notes where

foo : ℕ → ℝ

ℕ : Set

ℝ : Set

fooT : Set₁
fooT = ℕ → ℝ

fooTT : Set₂
fooTT = fooT → fooT

fooTTT : Setω₁
fooTTT = Set₁ → Set₂
