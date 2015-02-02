Theorem bag_count_sum : forall (n : nat) (s1 s2 : bag),
  count n (sum s1 s2) = count n s1 + count n s2.
Proof.
  intros n s1 s2. induction s1 as [| h1 s1'].
  Case "s1 = nil".
    reflexivity.
  Case "s1 = cons". induction s2 as [| h2 s2'].
    SCase "s2 = nil".
      rewrite app_nil_end. simpl. rewrite plus_0_r. reflexivity.
    SCase "s2 = cons".
      simpl. rewrite IHs1'. destruct (beq_nat h1 n). reflexivity.
    reflexivity.
Qed.
