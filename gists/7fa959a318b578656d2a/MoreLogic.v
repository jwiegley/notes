Theorem pigeonhole_principle : forall X (l1 l2 : list X),
  excluded_middle
    -> (forall x, appears_in x l1 -> appears_in x l2)
    -> length l2 < length l1
    -> repeats l1.
Proof.
  induction l1 as [|x xs IHxs]; intros l2 LEM Happ Hlen.
    inversion Hlen.

  destruct (LEM (appears_in x xs)).
    exact (repeats_head x xs H).
  apply repeats_tail.

  destruct (appears_in_app_split _ _ _ (Happ x (ai_here _ _))) as [? Hsplit].
  destruct Hsplit; subst.

  apply (IHxs (witness ++ witness0) LEM); clear IHxs; intros.
    destruct (LEM (x = x0)); subst.
      contradiction.

    apply app_appears_in.
    destruct (appears_in_app _ _ _ _ (Happ _ (ai_later _ _ _ H0))) as [|H2].
      left; assumption.
    inversion H2; subst.
      contradiction.
    right; assumption.

  rewrite app_length in *.
  apply Le.le_S_n.
  rewrite plus_n_Sm.
  assumption.
Qed.
