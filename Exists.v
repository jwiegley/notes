Lemma amrvimias : forall t : Set -> Prop,
  (exists x, t x) <-> (forall y : Prop, (forall x, t x -> y) -> y).
Proof.
  split; intros.
    destruct H.
    apply (H0 x).
    apply H.
  apply H.
  intros.
  exists x.
  apply H0.
Qed.