Theorem surj_inv : forall (A B : Type) (f : A -> B),
  surjective A B f ->
  exists f' : B -> A, inverse A B f f'.
Proof.
  intros.
  unfold inverse, id_Dom.
  unfold surjective in H.
  eexists.
  extensionality x.
  specialize (H (f x)).
  inversion H.
  unfold compose.
