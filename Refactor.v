  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    unfold ballot_valid; intro.
    revert cand_fin.
    cut ({(forall c, In c cand_all -> b c > 0)} +
         {~ (forall c, In c cand_all -> b c > 0)}).
      intros.
      destruct H; intuition.
    induction cand_all as [|? ? [?|?]]; intuition; [firstorder|].
    destruct (le_gt_dec (b a) 0).
      right; intro.
      destruct (H a (or_introl eq_refl)); intuition.
    left; intros.
    destruct H; auto; congruence.
  Qed.
