Require Omega.
Require Import Coq.Arith.Compare.

Inductive T := R : {n | n < 256} -> T.

Theorem T_eq_dec : forall (t1 t2 : T), {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1; destruct s.
  intro t2.
  destruct t2; destruct s.
  assert ({x = x0} + {x <> x0}).
    generalize dependent x0.
    induction x.
      destruct x0.
        left.
        reflexivity.
      right.
      auto.
    destruct x0.
      right.
      auto.
    intro H.
    assert (x < 256). omega.
    assert (x0 < 256). omega.
    specialize (IHx H0 x0 H1).
    destruct IHx.
      left. auto.
    right. auto.
  destruct H.
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
