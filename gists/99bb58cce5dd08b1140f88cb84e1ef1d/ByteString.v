Lemma not_imply : classic -> forall (P Q:Prop), ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros.
  unfold classic in H.
  pose proof H.
  specialize (H1 (P -> Q)).
  apply imply_to_and.
  assumption.
Qed.
