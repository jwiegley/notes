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

Lemma Map_left_identity : forall r, Same r (Map (fun _ x => x) r).
Proof.
  unfold Map; split; intros.
    eexists b.
    intuition.
  do 2 destruct H.
  simpl in *.
  rewrite H0.
  assumption.
Qed.

Lemma Map_right_identity : forall r, Same (Map (fun _ x => x) r) r.
Proof.
  unfold Map; split; intros.
    do 2 destruct H.
    simpl in *.
    rewrite H0.
    assumption.
  eexists b.
  intuition.
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

(*
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

Lemma Finite_Subtract_r : forall T X x,
  ~ In T X x -> Finite T (Subtract T X x) -> Finite T X .
Proof.
  intros.
  apply Non_disjoint_union' in H.
  rewrite H in H0.
  assumption.
Qed.

Lemma Surjective_Subtract : forall T (X Y : Ensemble T) f x,
  Surjective X Y f -> Surjective X (Subtract T Y (f x)) f.
Proof.
  unfold Surjective; intros.
  inversion H0; clear H0.
  destruct (H _ H1) as [? [? ?]]; subst.
  exists x0; auto.
Qed.

Lemma Singleton_not_inv : forall (U : Type) (x y : U),
  ~ In U (Singleton U x) y -> x <> y.
Proof.
  unfold not; intros; subst.
  apply H.
  constructor.
Qed.

Lemma Surjective_Intersection : forall T (X Y : Ensemble T) f x,
  Surjective X Y f
    -> Surjective (Intersection _ X (Complement _ (fun x2 => f x2 = f x)))
                  (Subtract _ Y (f x)) f.
Proof.
  unfold Surjective; intros.
  inversion H0; clear H0.
  destruct (H _ H1) as [? [? ?]]; subst.
  exists x0; intuition.
  constructor; auto.
  unfold Complement, Ensembles.In, not; intros.
  apply H2.
  rewrite H3.
  constructor.
Qed.
*)

Lemma Finite_Add_Subtract : forall T (Y : Ensemble T) x,
  Finite _ (Add T (Subtract T Y x) x) -> Finite _ Y.
Proof.
  intros.
  eapply Finite_downward_closed; eauto with sets; intros ??.
  (* Jason Gross: To avoid the axiom of choice, you'd need a stronger version
     of [Finite], something like having a list of elements together with a
     mapping of elements of the type to indices of the list such that if an
     element of the type is in the subset, then it is equal to the element of
     the list at the corresponding index. In this case, everything is
     constructive, and you shouldn't need either ensemble-extensionality nor
     decidable equality. *)
  elim (classic (x = x0)); intros.
    subst; right; constructor.
  left; constructor; auto.
  unfold not; intros.
  contradiction H1.
  inversion H2.
  reflexivity.
Qed.

Lemma Surjective_Add_Subtract : forall T X Y f x,
  ~ In T X x
    -> Surjective (Add T X x) Y f
    -> Surjective X (Subtract T Y (f x)) f.
Proof.
  unfold Surjective; intros.
  inversion H1.
  destruct (H0 _ H2) as [? [? ?]]; subst; clear H0 H2.
  inversion H4; subst; clear H4.
    exists x0; intuition.
  inversion H0; subst; clear H0.
  contradiction H3.
  constructor.
Qed.

Lemma Surjection_preserves_Finite : forall A X Y f,
  Surjective X Y f -> Finite A X -> Finite A Y.
Proof.
  intros.
  generalize dependent Y.
  induction H0; intros.
    eapply Finite_downward_closed; eauto with sets; intros ??.
    firstorder.
  apply Surjective_Add_Subtract in H1; auto.
  specialize (IHFinite _ H1).
  eapply Finite_Add_Subtract.
  constructor.
  exact IHFinite.
  unfold not; intros.
  inversion H2.
  contradiction H4.
  constructor.
Qed.

Theorem Map_Finite : forall f `(_ : Finite _ r), Finite _ (Map f r).
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

Print Assumptions Map_Finite.

Require Import Coq.Lists.List.

Definition Finite0 {A} (X : Ensemble A) : Type :=
  { xs : list A
  & { f : A -> option nat
    | forall x,
        Ensembles.In A X x
        <-> match f x with
            | None => False
            | Some i => nth_error xs i = Some x
            end } }.

Definition Finite1 {A} (X : Ensemble A) : Type :=
  { xs : list A | Same_set A X (fun x => List.In x xs) }.

Require Import Coq.Sorting.Permutation.

Theorem Finite0_Finite1 : forall A (X : Ensemble A),
  forall (x : Finite0 X) (y : Finite1 X),
    Permutation (projT1 x) (proj1_sig y).
Proof.
  intros.
  destruct x, y, s, s0; simpl.
  generalize dependent x0.
  induction x; intros.
    destruct x0; simpl in *.
      reflexivity.
    specialize (i a).
    destruct (x1 a);
    unfold Included, Ensembles.In in *;
    specialize (i0 a);
    specialize (i1 a);
    intuition;
    apply nth_error_In in H2;
    inversion H2.
Abort.

End Map.