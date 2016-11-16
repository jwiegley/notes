  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    intro.
    unfold ballot_valid.
    revert cand_fin.
    cut ({(forall c : cand, In c cand_all -> b c > 0)} +
         {~ (forall c : cand, In c cand_all -> b c > 0)}).
      intros.
      destruct H; firstorder.
    induction cand_all.
      firstorder.
    destruct IHl.
      destruct (le_gt_dec (b a) 0).
        right; intro.
        specialize (H a (or_introl eq_refl)).
        intuition.
      left; intros.
      destruct H; auto; congruence.
    firstorder.
  Qed.
