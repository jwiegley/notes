module hello where

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + x = x
succ x + y = succ (x + y)
