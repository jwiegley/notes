Lemma foo : forall p, ~~(~~p -> p).
Proof.
  intros p H.
  apply H.
  intro.
  elimtype False.
  apply H0.
  intro.
  apply H.
  intro.
  exact H1.
Qed.
Print foo.
