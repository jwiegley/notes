Lemma length_of_nil : forall X (l : list X), length l = 0 -> l = nil.
Proof. intros. destruct l. reflexivity. inversion H. Qed.

Theorem rev_pal_length : forall X n l, length l <= n -> l = rev l -> pal X l.
Proof.
  intros. induction n.
    replace l with (@nil X).
      constructor.
    inversion H.
    symmetry.
    apply length_of_nil.
    assumption.
  apply IHn.
Admitted.
