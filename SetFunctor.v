Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Data.Functor.
Require Import Coq.Sorting.Sorted.

Require Import mathcomp.ssreflect.path.

Generalizable All Variables.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive Compare := Lt | Eq | Gt.

Class Ord (a : Type) := {
  compare : a -> a -> Compare
}.
Arguments compare {a _} _ _.

Definition is_lt `{Ord a} :=
  fun x y : a => if compare x y is Lt then true else false.

Fixpoint memberOrd `{Ord a} (x : a) (s : seq a) : bool :=
  match s with
  | [::] => false
  | y :: ys => if compare x y is Eq
               then true
               else memberOrd x ys
  end.

Fixpoint uniqOrd `{Ord a} (s : seq a) : bool :=
  match s with
  | [::] => true
  | x :: s' => memberOrd x s' && uniqOrd s'
  end.

(* We model Haskell's Data.Set with a list that is always sorted, and always
   free of duplicate elements. *)
Record OrdSet (a : Type) := {
  carrier       : seq a;
  always_sorted : forall `{Ord a}, StronglySorted is_lt carrier;
  always_uniq   : forall `{Ord a}, uniqOrd carrier
}.

Section OrdFunctor.

Context {LookupOrd : forall a, Ord a}.

(* This axiom, that equality by Ord is is Leibnitzian, is key to making OrdSet
   a functor. *)
Axiom structured : forall {a} `{Ord a} {b} `{Ord b} (f : a -> b) (x y : a),
  compare x y = compare (f x) (f y).

Program Instance OSet_Functor : Functor OrdSet.
Obligation 1.
  destruct X0.
  pose (LookupOrd a).
  pose (LookupOrd b).
  pose (map X carrier0).
  refine (Build_OrdSet b l _ _).
  - intros.
    unfold l.
    specialize (always_sorted0 o).
    specialize (always_uniq0 o).
    induction carrier0; simpl in *.
      constructor.
    constructor.
      inversion always_sorted0.
      move/andP in always_uniq0.
      inversion always_uniq0.
      apply IHcarrier0; assumption.
    inversion always_sorted0.
    clear -H3.
    induction carrier0; simpl.
      constructor.
    inversion H3; subst.
    constructor.
      unfold is_lt.
      rewrite <- (structured X a0 a1). (* here is the magic *)
      apply H2.
    apply IHcarrier0.
    assumption.
  - intros.
    unfold l.
    specialize (always_sorted0 o).
    specialize (always_uniq0 o).
    induction carrier0; simpl in *.
      constructor.
    move/andP in always_uniq0.
    inversion always_sorted0.
    inversion always_uniq0.
    apply/andP.
    subst.
    split.
      clear -H4.
      induction carrier0; simpl in *; auto.
      rewrite <- (structured X a0 a1). (* here is the magic *)
      destruct (compare a0 a1);
      try apply IHcarrier0; assumption.
    clear -H5.
    induction carrier0; simpl in *; auto.
    move/andP in H5.
    inversion H5; clear H5.
    apply/andP.
    split.
      clear -H0.
      induction carrier0; simpl in *; auto.
      rewrite <- (structured X a0 a1). (* here is the magic *)
      destruct (compare a0 a1);
      try apply IHcarrier0; assumption.
    apply IHcarrier0.
    assumption.
Defined.

End OrdFunctor.

Module OrdFunctorLaws.

Require Import FunctionalExtensionality.

Include ListLaws.

Context {LookupOrd : forall a, Ord a}.

Program Instance OrdSet_FunctorLaws : @FunctorLaws OrdSet (@OSet_Functor LookupOrd).
Obligation 1.
  move=> x /=.
  unfold OSet_Functor_obligation_1.
  rewrite map_id.
  elim=> [|x xs IHxs] //=.
  simpl in IHxs.
  rewrite /sortEq.
  move=> x.
  induction x
  unfold 

Program Instance OSet_ApplicativeLaws :
    @ApplicativeLaws OSet (@OSet_Applicative LookupOrd).

Program Instance OSet_MonadLaws : @MonadLaws OSet (@Set_Monad LookupOrd).

End OrdMandLaws.