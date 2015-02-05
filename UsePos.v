(* A simple nat-indexed Vec type *)
Inductive Vec (x : Type) : nat -> Type :=
 | vec_nil : Vec x 0
 | vec_cons n : x -> Vec x n -> Vec x (S n).

Require Import Coq.Program.Equality.

(* I want to prove that if a Vec's number is 1, it must be a cons and a nil *)
Theorem vec_sole_exists A (vs : Vec A 1)
    : exists (v : A), vs = @vec_cons A 0 v (vec_nil A).
Proof.
  dependent destruction vs.
  exists a.
  f_equal.
  dependent destruction vs.
  reflexivity.
Qed.
