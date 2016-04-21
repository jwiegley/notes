Add Parametric Morphism (A : Type) : (@ex A)
  with signature ((eq ==> iff) ==> iff)
  as ex_intro_eq.
Proof.
  intros.
  split; intros;
  destruct H0;
  exists x0;
  specialize (H x0 x0 eq_refl);
  apply H;
  assumption.
Qed.

Lemma baz : exists n:nat, S n + 1 = S n.
Proof.
  setoid_rewrite Plus.plus_comm.
