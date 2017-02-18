Require Export Coq.Unicode.Utf8.
Require Export FunctionalExtensionality.

Set Universe Polymorphism.

Section LogicalQuantification.

Lemma forall_not_exists : (∀ x : Prop, x) ↔ (¬ ∃ x : Prop, ¬ x).
Proof.
  intuition; eauto.
  apply H.
  firstorder.
  contradiction (H x).
  intros.
  eapply H; eauto.
Qed.

Lemma not_forall_not_exists : (¬ ∀ x : Prop, x) ↔ (∃ x : Prop, ¬ x).
Proof.
  intuition; eauto.
  apply H0.
Qed.

Lemma exists_not_forall : (  ∃ x, x) ↔ (¬ ∀ x, ¬ x).
Proof. intuition; eauto. Qed.

Lemma not_exists_not_forall : (¬ ∃ x, x) ↔ (  ∀ x, ¬ x).
Proof. intuition; eauto. Qed.

End LogicalQuantification.

Section Quantification.

Variable r : Prop.

Notation "¬ x" := (x → r) (at level 75, right associativity).

Lemma fun_forall_not_exists : (∀ x : Prop, x) ↔ (¬ ∃ x, ¬ x).
Proof.
  intuition; eauto.
  apply H.
  firstorder.
  contradiction (H r).
  intros; assumption.
Qed.

Lemma fun_not_forall_not_exists : (¬ ∀ x : Prop, x) ↔ (∃ x, ¬ x).
Proof.
  intuition; eauto.
  apply H0.
Qed.

Lemma fun_exists_not_forall : (∃ x, x) ↔ (¬ ∀ x, ¬ x).
Proof. intuition; eauto. Qed.

Lemma fun_not_exists_not_forall : (¬ ∃ x, x) ↔ (  ∀ x, ¬ x).
Proof. intuition; eauto. Qed.

End Quantification.

Definition Ex := ∃ x, x.

Inductive Exists := Here : ∀ x, x → Exists.

Definition Exists' := ∀ r, (∀ x, x → r) → r.

(*
Lemma existence_implied : Exists <-> Exists'.
Proof.
  unfold Exists'; split; intros.
    eapply H0; eauto.
  apply H; intros.
  econstructor; eauto.
Qed.
*)

Definition phi (x : Exists) : Exists' :=
  match x with Here T t => fun _ k => k T t end.

Definition psi (x : Exists') : Exists := x Exists Here.

Lemma psi_phi : forall x : Exists, psi (phi x) = x.
Proof.
  unfold psi, phi; intros.
  destruct x; auto.
Qed.

Lemma phi_psi : forall x : Exists', phi (psi x) = x.
Proof.
  unfold Exists', phi, psi; intros.
  destruct (x Exists Here).
  extensionality r.
  extensionality t.
Abort.
