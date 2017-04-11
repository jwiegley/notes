module tfix where

open import Data.Unit
open import Data.Product

data Desc : Set₁ where
  arg : (A : Set) (d : A → Desc) → Desc
  rec : (r : Desc) → Desc
  ret : Desc

infix 5 ⟦_⟧_
⟦_⟧_ : Desc → Set → Set
⟦ arg A d ⟧ X = Σ[ a ∈ A ] ⟦ d a ⟧ X
⟦ rec d   ⟧ X = X × ⟦ d ⟧ X
⟦ ret     ⟧ X = ⊤

data Fix (d : Desc) : Set where
  ⟨_⟩ : ⟦ d ⟧ (Fix d) → Fix d

open import Data.Bool
open import Function

t : Desc
t = arg Bool λ { true  {- TInt -}   → ret
               ; false {- TArrow -} → rec $ rec ret }

fixt : Set
fixt = Fix t

pattern TInt       = ⟨ true , tt ⟩
pattern TArrow a b = ⟨ false , a , b , tt ⟩

Int→Int : fixt
Int→Int = TArrow TInt TInt