Lemma selsort_perm:
  forall n l, length l = n -> Permutation l (selsort l n).
Proof.
  intros.
  generalize dependent n.
  induction l as [| x xs]; intros; subst; simpl.
  - constructor.
  - specialize (IHxs x).
    destruct (select x xs).
