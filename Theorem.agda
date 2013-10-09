module Theorem where

open import Data.Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- 0≡n*n : ∀ n → 0 ≡ n * n → n ≡ 0
-- 0≡n*n zero h = refl
-- 0≡n*n (suc n) ()

lemma-+0 : ∀ n → n + zero ≡ n
lemma-+0 zero = refl
lemma-+0 (suc n) = cong suc (lemma-+0 n)

0≡n*n : ∀ n → 0 ≡ n → 0 ≡ n * n
0≡n*n zero h = refl
0≡n*n (suc n) ()

sqrt2 : ∀ n m → n * n ≡ 2 * m * m → m ≡ 0
sqrt2 zero m p =
    begin
        m
    ≡⟨ trans {!!} (0≡n*n m {!!}) ⟩
        m * m
    ≡⟨ {!!} ⟩
        0
    ∎
sqrt2 (suc n) m p = {!!}
    -- begin
    --     m
    -- ≡⟨ {!!} ⟩
    --     0
    -- ∎
