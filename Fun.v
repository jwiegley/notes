Lemma choose_fun_left :
      forall (A : Type)
             (n1 n2 : nat)
             (F1 : forall i, i < n1 -> A)
             (F2 : forall i, i < n2 -> A)
             (i : nat)
             (i_lt_n1 : i < n1),
             choose_fun A n1 n2 F1 F2 i (lt_plus_trans i n1 n2 (i_lt_n1)) = F1 i i_lt_n1.
Proof.
  intros A n1 n2 F1 F2 i i_lt_n1.
  generalize dependent n2.
  induction n1; simpl; intros.
    destruct n2; omega.
  admit.
Qed.