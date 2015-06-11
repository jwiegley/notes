Lemma dfeuer : forall (A B : Type) (g : B -> A) (f : A -> B),
  injective f -> cancel g f -> bijective f.
Proof.
  move=> A B g f Hinj Heqe.
  pose H := inj_can_sym Heqe Hinj.
  exact: Bijective H Heqe.
Qed.

