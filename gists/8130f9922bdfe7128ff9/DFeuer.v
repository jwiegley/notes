Theorem arkeet :
  ~ (forall A B (f : A -> B), injective f -> exists g, cancel f g).
Proof.
  move=> H.
  have H0 : injective (fun _ : False => tt).
    by move=> *; contradiction.
  destruct (H False unit (fun (_ : False) => tt) H0).
  exact/x/tt.
Qed.
