Theorem insert_perm_l: forall l i, Permutation (i::l) (insert i l).
Proof.
  intros. induction l as [| x xs].
  reflexivity.
  simpl. destruct (ble_nat i x).
    reflexivity.
    rewrite <- IHxs. apply perm_swap.
Qed.

Theorem insert_perm: forall l l' i,
  Permutation l l' -> Permutation (i::l) (insert i l').
Proof.
  intros. destruct l' as [| y ys].
    simpl. apply perm_skip. apply H.
    destruct l.
      apply Permutation_nil in H. rewrite H. reflexivity.
      rewrite H. apply insert_perm_l.
Qed.
