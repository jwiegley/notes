Lemma ceval_equiv:
  (* Or: If there are no WHILEs present, then ceval_fun_no_while is equivalent
     to ceval. *)
  forall c st, no_whiles c = true -> ceval c st (ceval_fun_no_while st c).
Proof.
  intros.
  generalize dependent st.
  induction c; intros; simpl.
  Case "skip". apply E_Skip.
  Case "::=". apply E_Ass. reflexivity.
  Case ";;".
    simpl in H. apply andb_true_iff in H. inversion H.
    apply E_Seq with (st' := (ceval_fun_no_while st c1)).
      apply IHc1. assumption.
    apply IHc2. assumption.
  Case "if".
    simpl in H. apply andb_true_iff in H. inversion H.
    destruct b; simpl.
      apply E_IfTrue; auto.
      apply E_IfFalse; auto.
      admit.
      admit.
      admit.
      admit.
  Case "while".
    inversion H.
Qed.
