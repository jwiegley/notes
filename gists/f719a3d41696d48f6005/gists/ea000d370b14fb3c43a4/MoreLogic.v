Lemma filter_challenge_2 : forall {X} (test : X -> bool) (l m : list X),
  is_subseq m l -> forallb test m = true -> length m <= length (filter test l).
Proof.
  intros X test l.
  induction l as [| x xs]; intros; simpl;
  inversion H; subst; simpl;
  try (apply Le.le_0_n).
  - elim_truth.
    apply Le.le_n_S.
    apply IHxs. assumption.
    elim_truth.
  - destruct (test x);
    try (apply le_succ);
    apply IHxs; assumption.
Qed.
