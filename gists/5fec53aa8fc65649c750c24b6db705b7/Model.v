Lemma not_inj (φ ψ : LTL) : (φ ≈ ψ) -> ¬φ ≈ ¬ψ.
Proof. intros; now rewrite H. Qed.

Lemma not_until (φ ψ : LTL) : ¬ (φ U ψ) ≈ ¬φ R ¬ψ.
Proof.
  rewrite <- Complement_Complement.
  apply not_inj.
  split; repeat intro; unfold In in *.
  - dependent induction H.
    + dependent induction H0.
      * contradiction.
      * contradiction.
    + apply release_inv in H1.
      destruct H1.
      destruct H2.
      * contradiction.
      * rewrite tail_cons in H2.
        intuition.
  - (* now need to prove ¬ (¬φ R ¬ψ) ≈ φ U ψ *)
Admitted.
