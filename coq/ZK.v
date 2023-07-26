Require Import Coq.Unicode.Utf8.

(* Typically, for the equality proof to be believable by another system, it is
   represented using an algebraic intermediate representation (AIR) of the
   function's evaluation. *)
Definition Circuit {a b : Type} (f : a -> b) :=
  ∀ x : a, ∃ y : b, f x = y.
