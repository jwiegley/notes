Lemma expand_until (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X (φ U ψ)).
Admitted.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  rewrite expand_until.
  split; repeat intro; unfold In in *.
  - apply not_or in H.
    destruct H.
    apply not_and in H0.
    destruct H0;
    unfold In in *.
    + now left.
    + left; auto.
      (* stuck again *)
Admitted.
