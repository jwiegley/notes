Require Import Coq.omega.Omega.

Axiom my_custom_ind : forall m P, P m -> (forall n, P (S n) -> P n) -> forall n, 0 <= m -> P n.

Arguments my_custom_ind m _ _ _ _ _ : clear implicits.

Lemma foo:
  forall a b c,
  b < c -> a <= b -> a < c.
Proof.
  intros.
  generalize dependent a.
  induction a using (@my_custom_ind _ _ _ _ _ _).
Qed.
