Require Import Coq.Vectors.Vector.

Lemma Forall_tail :
  forall {A} {n} P x (xs: t A n), Forall P (cons _ x _ xs) -> Forall P xs.
Proof.
  intros.
  inversion H.
  dependent rewrite <- H2.
  assumption.
Qed.
