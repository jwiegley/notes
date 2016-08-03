Require Export
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts.

Require Import
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Setoids.Setoid.

Generalizable All Variables.

Section Map.

Variables A B : Type.

Definition Lookup (a : A) (b : B) (r : Ensemble (A * B)) := In _ r (a, b).

Definition Same (x y : Ensemble (A * B)) : Prop :=
  forall a b, Lookup a b x <-> Lookup a b y.

Definition Map (f : A -> B -> B) (r : Ensemble (A * B)) : Ensemble (A * B) :=
  fun p => exists b : B, Lookup (fst p) b r /\ snd p = f (fst p) b.

Lemma Map_identity : forall r, Same r (Map (fun _ x => x) r).
Proof.
  unfold Map; split; intros.
    eexists b.
    intuition.
  do 2 destruct H.
  simpl in *.
  rewrite H0.
  assumption.
Qed.

Lemma Map_composition : forall f g r,
  Same (Map (fun k e => f k (g k e)) r) (Map f (Map g r)).
Proof.
  unfold Map; split; intros.
    destruct H.
    destruct H; simpl in *.
    subst.
    exists (g a x); simpl in *.
    split; trivial.
    exists x; simpl.
    intuition.
  destruct H.
  destruct H; simpl in *.
  subst.
  destruct H; simpl in *.
  exists x0; simpl in *.
  destruct H.
  intuition.
  rewrite <- H0.
  reflexivity.
Qed.

(* Jason Gross: You need to use the fact that there is a surjection from [r]
   onto your conclusion ensemble: map [p] to [(fst p, f (fst p) (snd p))].
   Then prove that if you have a surjection [X ↠ Y], then [Finite X -> Finite
   Y]. *)

Definition Surjective {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall y : B, In _ Y y -> exists x : A, In _ X x /\ y = f x.

Definition Injective {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall (x y : A), In _ X x -> In _ X y -> f x = f y
    -> In _ Y (f x) /\ In _ Y (f y) /\ x = y.

Lemma split_set T (X : Ensemble T) x : In T X x
  -> let X' := (Subtract _ X x) in
     Same_set _ (Add _ X' x) X /\ ~ In _ X' x.
Proof.
  intro Hin.
  split.
  { split; [ apply add_soustr_1 | apply add_soustr_2 ]; assumption. }
  { intro H'; apply Subtract_inv in H'; intuition congruence. }
Qed.

Program Instance Finite_Proper {A} :
  Proper (Same_set A --> Basics.flip Basics.impl) (Finite A).
Obligation 1.
  unfold Basics.flip, Basics.impl.
  intros ????.
  eapply Finite_downward_closed; eauto with sets; intros ??.
  apply H.
  assumption.
Qed.

Lemma Finite_Subtract : forall T X x,
  Finite T X -> Finite T (Subtract T X x).
Proof.
  intros.
  eapply Finite_downward_closed; eauto with sets; intros ??.
  inversion H0.
  assumption.
Qed.

Theorem Surjection_preserves_Finite : forall A X Y f,
  Surjective X Y f -> Finite A X -> Finite A Y.
Proof.
  unfold Surjective; intros.
  generalize dependent Y.
  induction H0; intros.
    eapply Finite_downward_closed; eauto with sets; intros ??.
    firstorder.
  elim (classic (In A0 Y (f x))); intro H'0; auto with sets.
    destruct (split_set _ _ _ H'0); clear H'0.
    rewrite <- H2; clear H2.
    constructor; auto.
    apply Finite_Subtract.
    apply IHFinite; intros.
    destruct (H1 _ H2) as [? [? ?]]; subst.
    inversion H4; subst; clear H4.
      eauto.
    inversion H5; subst; clear H5.
    admit.
  apply IHFinite; intros.
  destruct (H1 _ H2), H3.
  inversion H3; subst; clear H3.
    exists x0.
    intuition; subst.
  inversion H5; subst; clear H5.
  contradiction.
Admitted.

Lemma Map_Finite : forall f `(_ : Finite _ r), Finite _ (Map f r).
Proof.
  unfold Map; intros.
  apply Surjection_preserves_Finite
   with (X:=r) (f:=fun p => (fst p, f (fst p) (snd p))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (a, x); simpl.
  intuition.
Qed.

End Map.