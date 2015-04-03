Theorem skipn_succ : forall A (n:nat) (l:list A),
  length (skipn n l) >= length (skipn (S n) l).
Proof.
  intros.
  generalize dependent n.
  induction l; simpl; intros.
    apply Le.le_0_n.
  unfold ge in *.
  destruct n.
    simpl; auto.
  specialize (IHl n).
  rewrite IHl.
  rewrite skipn_head.
  auto.
Qed.
