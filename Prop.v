Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof. induction l1; intros; simpl; auto. Qed.

Lemma length_snoc : forall X x (l : list X),
  length (snoc l x) = S (length l).
Proof.
  intros.
  rewrite snoc_append.
  rewrite app_length.
  rewrite plus_comm. auto.
Qed.

Lemma rev_pal_length : forall X n l, length l <= n -> l = rev l -> pal X l.
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
    rewrite length_snoc in H.
    apply Le.le_Sn_le. assumption.
  rewrite rev_snoc in Heqe.
  inversion Heqe.
  rewrite H2 at 2. reflexivity.
Qed.

Theorem rev_pal : forall X (l : list X), l = rev l -> pal X l.
Proof. intros. apply (rev_pal_length X (length l)); auto. Qed.
