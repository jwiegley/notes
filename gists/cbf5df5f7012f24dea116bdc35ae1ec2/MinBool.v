Require Import
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.SetoidClass.

(***********************************************************************
 * This is a minimal Boolean Logic comprised of ∨, ¬ and five axioms.
 *
 * NOTE: It is possible to formulate the following using a single axiom:
 *
 *   forall (φ ψ χ ρ : t),
 *     ¬(¬(¬(φ ∨ ψ) ∨ χ) ∨ ¬(φ ∨ ¬(¬χ ∨ ¬(χ ∨ ρ)))) ≈ χ
 *
 * However, the proofs of the five axioms below in terms of this single one
 * are laborious and left as an exercise to the motivated reader. Further
 * notes may be found in the paper "Short Single Axioms for Boolean Algebra"
 * by McCune, et al.: https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf
 *)

Reserved Notation "f ≈ g" (at level 79).
Reserved Notation "¬ p"   (at level 0).
Reserved Infix    "∨"     (at level 46, right associativity).
Reserved Notation "⊤"     (at level 0).
Reserved Notation "⊥"     (at level 0).

Class MinimalBooleanLogic {t : Type} := {
  is_setoid :> Setoid t;

  not   : t -> t      where "¬ p" := (not p);
  or    : t -> t -> t where "∨"   := (or);
  true  : t           where "⊤"   := (true);
  false : t           where "⊥"   := (false);

  not_respects : Proper (equiv ==> equiv) not;
  or_respects  : Proper (equiv ==> equiv ==> equiv) or;

  true_def  {φ : t} : ⊤ ≈ φ ∨ ¬ φ;
  false_def {φ : t} : ⊥ ≈ ¬ (φ ∨ ¬ φ);

  (** This is one set of fundamental axioms of boolean algebra.
      "and" is not fundamental, and can be defined in terms of "or". *)
  or_true      {φ     : t} : φ ∨ ⊤ ≈ ⊤;
  or_false     {φ     : t} : φ ∨ ⊥ ≈ φ;
  or_comm      {φ ψ   : t} : φ ∨ ψ ≈ ψ ∨ φ;
  or_assoc     {φ ψ χ : t} : (φ ∨ ψ) ∨ χ ≈ φ ∨ (ψ ∨ χ);
  or_distr_not {φ ψ χ : t} : ¬ (¬ (φ ∨ ψ) ∨ ¬ (φ ∨ χ)) ≈ φ ∨ ¬ (¬ ψ ∨ ¬ χ);
}.
