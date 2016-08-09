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

Definition Map' {C} (f : A -> B -> C -> Prop) (r : Ensemble (A * B)) :
  Ensemble (A * C) :=
  fun p => exists b : B, Lookup (fst p) b r /\ f (fst p) b (snd p).

End Map.

Arguments Lookup : default implicits.
Arguments Same : default implicits.
Arguments Map' : default implicits.

Ltac t H :=
  unfold Map'; split; intros;
  repeat destruct H; simpl in *; subst;
  firstorder.

Lemma Map'_left_identity : forall A B (r : Ensemble (A * B)),
  Same r (Map' (fun _ x x' => x = x') r).
Proof. t H. Qed.

Lemma Map'_right_identity : forall A B (r : Ensemble (A * B)),
  Same (Map' (fun _ x x' => x = x') r) r.
Proof. t H. Qed.

Lemma Map'_composition :
  forall A B C D (f : A -> C -> D -> Prop) (g : A -> B -> C -> Prop) r,
    Same (Map' (fun k (e : B) (e' : D) =>
                  exists e'' : C, g k e e'' /\ f k e'' e') r)
         (Map' f (Map' g r)).
Proof. t H. Qed.

Definition Surjective {A B} (X : Ensemble A) (Y : Ensemble B) f :=
  forall y : B, In _ Y y -> exists x : A, In _ X x /\ y = f x.

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

Lemma Surjective_Add_Subtract :
  forall T T' (X : Ensemble T) (Y : Ensemble T') f x,
    ~ In T X x
      -> Surjective (Add T X x) Y f
      -> Surjective X (Subtract T' Y (f x)) f.
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

Lemma Surjection_preserves_Finite : forall T T' X Y f,
  Surjective X Y f -> Finite T X -> Finite T' Y.
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

Theorem Map'_Finite :
  forall A B C (f : A -> B -> C -> Prop) `(_ : Finite _ r)
         (is_total : forall (k : A) (x : B), { y : C | f k x y })
         (is_functional : forall (k : A) (x : B) (y y' : C),
                            f k x y -> f k x y' -> y = y'),
  Finite _ (Map' f r).
Proof.
  unfold Map'; intros ???? r ? k g.
  apply Surjection_preserves_Finite
   with (X:=r) (f:=fun p => (fst p, proj1_sig (k (fst p) (snd p)))); trivial.
  intros ??.
  unfold Ensembles.In in H.
  do 2 destruct H.
  destruct y; simpl in *; subst.
  exists (a, x); simpl.
  destruct (k a x); simpl.
  intuition.
  f_equal.
  eapply g; eauto.
Qed.

Print Assumptions Map'_Finite.

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
