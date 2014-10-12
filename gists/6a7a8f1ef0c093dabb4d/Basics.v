Lemma plus_inj : forall n m o, n + o = m + o -> n = m.
Proof.
  intros. induction o.
    repeat rewrite <- plus_n_O in H.
    assumption.
  apply IHo.
  repeat rewrite <- plus_n_Sm in H.
  inversion H.
  reflexivity.
Qed.
