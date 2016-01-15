    (* method: pop *)
    {
      unfold pop.
      destruct r_o as [n v].
      unfold VecAsList_AbsR in H0.
      subst H.
      instantiate (1 := fun r_n =>
                          match r_n with
                          | nil => ret (nil, None)
                          | cons x xs => ret (xs, Some x)
                          end).
      destruct r_n; simpl.
        destruct n.
          simplify with monad laws; simpl.
          rewrite H0.
          refine pick eq.
          simplify with monad laws; simpl.
          reflexivity.
        destruct v as [x' v']; simpl;
        rewrite vec_seq_cons in H0.
        discriminate.
      destruct n.
        destruct v.
        simpl in H0.
        discriminate.
      destruct v as [x' v']; simpl;
      simplify with monad laws; simpl.
      rewrite vec_seq_cons in H0.
      inversion H0.
      rewrite H2.
      refine pick eq.
      simplify with monad laws; simpl.
      reflexivity.
    }

    finish_SharpeningADT_WithoutDelegation.
  Defined.
