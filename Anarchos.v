Inductive T := R : {n | n < 256} -> T.

Theorem T_eq_dec : forall (t1 t2 : T), {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1; destruct s.
  intro t2.
  destruct t2; destruct s.
  destruct (Peano_dec.eq_nat_dec x x0).
    left.
    f_equal.
    revert l l0.
    rewrite e; clear e x.
    intros l l0.
    f_equal.
    apply Peano_dec.le_unique.
  right.
  intro H.
  inversion H.
  contradiction.
Qed.
