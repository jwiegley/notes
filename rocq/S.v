Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.SetoidTactics.

Parameter A : Set.
Axiom A_setoid : Setoid A.

Theorem t : forall a b c : A, a = b -> c = a -> b = c.
Proof.
  congruence.
Qed.

Theorem t' : forall a b c : A, a == b -> c == a -> b == c.
Proof.
  intros. transitivity a; symmetry; assumption.
Qed.