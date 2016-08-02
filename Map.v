Require Export
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts.

Require Import
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Setoids.Setoid
  Here.Same_set.

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

Definition Surjection {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall y : B, In _ Y y -> exists x : A, In _ X x /\ y = f x.

Theorem Surjection_preserves_Finite : forall A X Y f,
  Surjection X Y f -> Finite A X -> Finite A Y.
Proof.
  unfold Surjection; intros.
  induction H0.
    eapply Finite_downward_closed; eauto with sets; intros ??.
    firstorder.
  apply IHFinite; intros.
  specialize (H y H2).
  do 2 destruct H.
  inversion H; subst; clear H.
    exists x0.
    intuition; subst.
  inversion H4; subst; clear H4.
Abort.

Lemma Map_Finite : forall f `(_ : Finite _ r), Finite _ (Map f r).
Proof.
  unfold Map, Lookup; intros.
Abort.

End Map.