Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros.
  generalize dependent n.
  induction l as [| x xs].
  Case "l = nil".
    intros. inversion H. reflexivity.
  Case "l = cons".
    intros. rewrite <- IHxs.
    simpl. apply app_length_cons with (x := x).
