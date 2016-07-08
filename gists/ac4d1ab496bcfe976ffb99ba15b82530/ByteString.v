Definition classic := forall P :  Prop, ~~P -> P.

Lemma not_imply : classic -> forall (P Q:Prop), ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros.
  unfold classic in H.
  pose proof H.
  specialize (H1 (P -> Q)).
  contradiction H0.
  apply H1.
Abort.
