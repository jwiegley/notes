Lemma fold_len_distr : forall (X : Type) (l1 l2 : list X),
  fold_length (l1 ++ l2) = fold_length l1 + fold_length l2.
Proof.
  intros X l1 l2. induction l1 as [|n l1' IHl1'].
    + simpl. reflexivity.
    + unfold fold_length in *.
      simpl. rewrite IHl1'.
      reflexivity.
Qed.
