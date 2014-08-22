Theorem rev_pal_length : forall X n l, length l <= n -> l = rev l -> pal X l.
Proof.
  induction n; intros.
    inversion H.
    destruct l; [ constructor | inversion H2 ].
  destruct l. constructor.
  simpl in *.
  apply Le.le_S_n in H.
  rewrite H0.
  destruct (rev l) eqn:Heqe. constructor.
  inversion H0; subst.
  constructor.
  apply IHn.
    assert (length (snoc l0 x0) = S (length l0)).
      rewrite snoc_append.
      rewrite app_length.
      rewrite plus_comm. auto.
    rewrite H1 in H.
    apply Le.le_Sn_le. assumption.
  rewrite rev_snoc in Heqe.
  inversion Heqe.
  rewrite H2 at 2. reflexivity.
Qed.
