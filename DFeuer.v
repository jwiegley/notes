Theorem arkeet :
  ~ (forall A B (f : A -> B), injective f -> exists g, cancel f g).
Proof.
  move=> H.
  have H0 : injective (fun _ : False => tt).
    rewrite /injective.
    move=> x1 x2 Heqe.
    contradiction.
  specialize (H False unit (fun (_ : False) => tt) H0).
  destruct H.
  exact/x/tt.
Qed.
