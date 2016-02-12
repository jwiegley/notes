Require Import Hask.Ltac.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Cont.
Require Import Data.Functor.Identity.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** Isomorphisms *)

Definition isomorphic (X Y : Type) : Prop :=
  exists (f : X -> Y), exists (g : Y -> X),
      f \o g = id /\ g \o f = id.

Notation "X ≅ Y" := (isomorphic X Y) (at level 100).

Program Instance Iso_Equivalence : Equivalence isomorphic.
Obligation 1.
  intro x.
  exists id.
  exists id.
  unfold id; firstorder.
Qed.
Obligation 2.
  firstorder.
Qed.
Obligation 3.
  intros x y z H1 H2.
  firstorder.
  exists (x1 \o x0).
  exists (x2 \o x3).
  rewrite comp_assoc.
  assert ((x1 \o x0) \o x2 = x1 \o (x0 \o x2)).
    rewrite comp_assoc.
    reflexivity.
  assert ((x2 \o x3) \o x1 = x2 \o (x3 \o x1)).
    rewrite comp_assoc.
    reflexivity.
  split.
    rewrite H3, H, <- H0.
    reflexivity.
  rewrite comp_assoc, H4, H2, <- H1.
  reflexivity.
Qed.

Add Parametric Relation {A B : Type} : Type isomorphic
  reflexivity proved by (@Equivalence_Reflexive _ _ Iso_Equivalence)
  symmetry proved by (@Equivalence_Symmetric _ _ Iso_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Iso_Equivalence)
  as isomorphic_relation.

(** Adjoint Functors *)

Definition adjoint (f g : Type -> Type) : Prop :=
  forall a b, f a -> b ≅ a -> g b.

Notation "F ⊣ G" := (adjoint F G) (at level 100).

(** Representable Functors *)

Definition representable (f : Type -> Type) : Prop :=
  forall a, exists R, R -> a ≅ f a.

(** Identity *)

Require Import FunctionalExtensionality.

Lemma identity_iso : forall (A : Type), Identity A ≅ A.
Proof. reflexivity. Qed.

Lemma Identity_representable : representable Identity.
Proof.
  intro a.
  exists unit.
  exists (fun k => k tt).
  exists (fun i u => i).
  unfold comp.
  split;
  extensionality x.
    reflexivity.
  extensionality u.
  destruct u.
  reflexivity.
Qed.

(** Codensity *)

Definition Codensity m a := forall r : Type, (a -> m r) -> m r.

Axiom Codensity_parametricity :
  forall `{Monad m} A B (k : Codensity m A) (f : A -> m B),
    k _ \o (fun x => x >=> f) = bind f \o k _.

Import MonadLaws.

Lemma codensity_iso : forall `{MonadLaws m} A, Codensity m A ≅ m A.
Proof.
  intros.
  exists (fun k => k _ pure).
  exists (fun x _ k => x >>= k).
  split.
    apply join_fmap_pure.
  extensionality k.
  extensionality r.
  extensionality p.
  pose proof (Codensity_parametricity A r k p).
  unfold comp, bind in *.
  apply equal_f with (x:=pure) in H1.
  rewrite <- H1.
  unfold kleisli_compose, bind, comp, id.
  f_equal.
  extensionality x.
  rewrite fmap_pure_x, join_pure_x.
  reflexivity.
Qed.

Axiom Cont_parametricity : forall A B (f : A -> B) (k : forall r, Cont r A),
  f (k _ id) = k _ f.

Lemma cont_iso : forall A, (forall r, Cont r A) ≅ A.
Proof.
  intros.
  unfold isomorphic.
  exists (fun k => k _ id).
  exists (fun x _ k => k x).
  split.
    extensionality x.
    reflexivity.
  extensionality k.
  extensionality r.
  extensionality p.
  unfold comp.
  apply Cont_parametricity.
Qed.

Axiom Yoneda_parametricity :
  forall `{Functor f} `(k : forall r, (a -> r) -> f r) `(p : a -> b),
    fmap p (k a id) = k b p.

Lemma yoneda_iso : forall `{FunctorLaws f} a, (forall r, (a -> r) -> f r) ≅ f a.
Proof.
  intros.
  exists (fun k => k _ id).
  exists (fun x _ f => fmap f x).
  unfold comp.
  split.
    extensionality x.
    rewrite fmap_id.
    reflexivity.
  extensionality k.
  extensionality r.
  extensionality p.
  apply Yoneda_parametricity.
Qed.

Definition Reader (e : Type) (a : Type) := e -> a.
Definition State (s : Type) (a : Type) := s -> (a * s).

Instance Impl_Functor {A} : Functor (fun B => A -> B) := {
  fmap := fun A B f run => fun xs => f (run xs)
}.

Instance Impl_Applicative {A} : Applicative (fun B => A -> B) := {
  pure := fun _ x => fun xs => x;
  ap   := fun A B runf runx => fun xs => runf xs (runx xs)
}.

Instance Impl_Monad {A} : Monad (fun B => A -> B) := {
  join := fun A run => fun xs => run xs xs
}.

Lemma codensity_reader_state : forall e a, Codensity (Reader e) a ≅ State e a.
Proof.
  intros.
  unfold Codensity, Reader, State, comp.
  unfold isomorphic.
  exists (fun (k : forall r : Type, (a -> e -> r) -> e -> r) s =>
            (k _ (fun x y => x) s, k _ (fun x y => y) s)).
  exists (fun k _ f e => match k e with (x,y) => f x y end).
  unfold comp.
  split.
    extensionality x.
    extensionality s.
    unfold id.
    destruct (x s).
    reflexivity.
  extensionality k.
  extensionality r.
  extensionality f.
  extensionality s.
  unfold id.
  pose proof (@Codensity_parametricity (Reader e) Impl_Monad a r k f).
  unfold comp in H.
  apply equal_f with (x:=pure) in H.
  unfold kleisli_compose, bind, comp, id in H.
  simpl in H.
  replace (fun (x : a) (xs : e) => f x xs) with f in H by trivial.
  rewrite H.
  f_equal.
  pose proof (@Codensity_parametricity (Reader e) Impl_Monad a e k (fun _ => id)).
  unfold comp in H0.
  unfold kleisli_compose, bind, comp, id in H0.
  simpl in H0.
  apply equal_f with (x:=pure) in H0.
  rewrite H0.
  reflexivity.
Qed.