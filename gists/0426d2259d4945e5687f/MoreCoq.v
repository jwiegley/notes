Definition split_combine_statement := forall X (l1 l2 : list X),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  unfold split_combine_statement. intros X l1.
  induction l1; intros; simpl;
    destruct l2; simpl; try inversion H; auto.
  rewrite IHl1. reflexivity.
  inversion H. reflexivity.
Qed.
