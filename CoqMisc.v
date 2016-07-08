Lemma Nlt_nat_lt : forall n m, (n < N.to_nat m)%nat -> (N.of_nat n < m).
Proof.
  intros.
  apply N2Z.inj_lt.
  rewrite nat_N_Z.
  apply Znat.inj_lt in H.
  rewrite N_nat_Z in H.
  exact H.
Qed.

Lemma Nle_nat_le : forall n m, (n <= N.to_nat m)%nat -> (N.of_nat n <= m).
Proof.
  intros.
  apply N2Z.inj_le.
  rewrite nat_N_Z.
  apply Znat.inj_le in H.
  rewrite N_nat_Z in H.
  exact H.
Qed.

Theorem Nrange_minus : forall off1 n x, off1 <= n < off1 + x -> n - off1 < x.
Proof.
  intros.
  destruct H.
  rewrite N2Z.inj_lt, N2Z.inj_sub; trivial.
  rewrite N2Z.inj_le in H.
  rewrite N2Z.inj_lt, N2Z.inj_add in H0.
  omega.
Qed.

Theorem Nsucc_nat : forall n, N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n).
Proof.
  induction n.
    reflexivity.
  constructor.
Qed.

Definition funType `(dom : Vector.t Type n) (cod : Type) : Type.
  induction dom.
    exact cod.
  exact (h -> IHdom).
Defined.
