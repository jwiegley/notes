module Swiftlet where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ)
import Data.Sign
open import Data.Integer using (ℤ; sign; _◃_; ∣_∣)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality

Name : Set
Name = String

mutual
  Context : Set
  Context = Name → Qual × Value

  Prog : Set
  Prog = List Struct × Expr

  Struct : Set
  Struct = Name × List Bind

  data Qual : Set where
    qlet, var : Qual

  Bind : Set
  Bind = Qual × Name × Type

  data Arg : Set where
    ref : Path → Arg
    arg : Expr → Arg

  data Expr : Set where
    _；_   : Expr → Expr → Expr
    _≔_𝑖𝑛_ : Bind → Expr → Expr → Expr
    _≔_   : Path → Expr → Expr
    [e]   : List Expr → Expr
    epath : Path → Expr
    eval  : Value → Expr
    ecall : Name → List Expr → Expr
    earg  : Expr → List Arg → Expr
    etern : Expr → Expr → Expr → Expr
    etyp  : Expr → Type → Expr

  data Param : Set where
    inout : Type → Param
    param : Type → Param

  data Type : Set where
    func  : List Param → Type → Type
    array : List Type → Type
    ty    : Name → Type
    Int   : Type
    Any   : Type
    unit  : Type

  data Path : Set where
    dot  : Expr → Name → Path
    sub  : Expr → Expr → Path
    lval : LValue → Path

  data Value : Set where
    lam  : List (Name × Param) → Expr → Value
    ctx  : Context → Value
    ary  : {n : ℕ} → Vec Value n → Value
    box  : Value → Value
    int  : ℤ → Value

  data LValue : Set where
    ldot  : LValue → Name → LValue
    lsub  : LValue → ℤ → LValue
    lname : Name → LValue

  data _,_⊢_⇓ᴿ_,_ (Δ : List Struct) :
    Context → Expr → Context → Value → Set
    where
    e-name
      : (μ : Context) (x : Name) (m : Qual) (v : Value)
      → μ x ≡ ( m , v )
      → Δ , μ ⊢ epath (lval (lname x)) ⇓ᴿ μ , v

    e-prop
      : (μ μ′ : Context) (e : Expr) (θˢ : Context)
      → Δ , μ ⊢ e ⇓ᴿ μ′ , ctx θˢ
      → (x : Name) (m : Qual) (v : Value)
      → θˢ x ≡ ( m , v )
      → Δ , μ ⊢ epath (dot e x) ⇓ᴿ μ , v

    e-elem
      : (μ μ′ : Context) (e₁ : Expr) (k : ℕ) (v : Vec Value k)
      → Δ , μ ⊢ e₁ ⇓ᴿ μ′ , ary v
      → (μ″ : Context) (e₂ : Expr) (z : ℤ)
      → Δ , μ′ ⊢ e₂ ⇓ᴿ μ″ , int z
      → sign z ≡ Data.Sign.+
      → (c : Fin k) (H : ∣ z ∣ Data.Nat.< k)
      → c ≡ Data.Fin.fromℕ< H
      → (vᵢ : Value) → vᵢ ≡ lookup v c
      → Δ , μ ⊢ epath (sub e₁ e₂) ⇓ᴿ μ″ , vᵢ

    e-inout
      : (μ μ′ : Context) (r : Path) (w : LValue)
      → Δ , μ ⊢ r ⇓ᴸ μ′ , var , w
      → Δ , μ ⊢ {!!} (ref r) ⇓ᴿ μ′ , {!!}

  data _,_⊢_⇓ᴸ_,_,_ (Δ : List Struct) :
    Context → Path → Context → Qual → LValue → Set
    where
    p-name
      : (μ : Context) (x : Name) (m : Qual) (v : Value)
      → μ x ≡ ( m , v )
      → Δ , μ ⊢ lval (lname x) ⇓ᴸ μ , m , lname x
