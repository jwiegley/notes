
module Term where

open import Prelude
open import Lists
open import Type public

Name = String

module Unchecked where

  data Term : Set where
    var : Name → Term
    lit : Nat → Term
    suc : Term
    app : Term → Term → Term
    lam : Name → Type → Term → Term

module WellTyped where

  Cxt = List (Name × Type)

  data Term : Cxt → Type → Set where
    var : ∀ {Γ a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    app : ∀ {Γ a b} (u : Term Γ (a => b)) (v : Term Γ a) →
            Term Γ b
    lam : ∀ {Γ} x a {b} (v : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
    lit : ∀ {Γ} (n : Nat) → Term Γ nat
    suc : ∀ {Γ} → Term Γ (nat => nat)

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  forgetTypes : ∀ {Γ a} → Term Γ a → Expr
  forgetTypes (var x i) = var x
  forgetTypes (app t t₁) = app (forgetTypes t) (forgetTypes t₁)
  forgetTypes (lam x a t) = lam x a (forgetTypes t)
  forgetTypes (lit n) = lit n
  forgetTypes suc = suc

module WellScoped where

  -- Exercise: Define well-scoped terms.
  Cxt = List Name

  data Term (Γ : Cxt) : Set where
    var : ∀ (x : Name) (i : x ∈ Γ) → Term Γ
    app : Term Γ → Term Γ → Term Γ
    lam : Name → Type → Term Γ → Term Γ
    lit : Nat → Term Γ
    suc : Term Γ

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  forgetScope : ∀ {Γ} → Term Γ → Expr
  forgetScope (var x _) = var x
  forgetScope (lit x) = lit x
  forgetScope suc = suc
  forgetScope (app t t₁) = app (forgetScope t) (forgetScope t₁)
  forgetScope (lam x a t) = lam x a (forgetScope t)
