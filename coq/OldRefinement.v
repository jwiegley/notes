Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Import VectorNotations.

Section Refinement.

Open Scope nat_scope.

(** This style of vector allows us to just induct on [nat]. *)
Fixpoint vec (A : Type) (n : nat) : Type :=
  match n with
  | O => unit : Type
  | S x => (A * vec A x)%type
  end.

Class Reflected
      (index : Type)
      (rich : index -> Type -> Type)
      (poor : Type -> Type) := {
  qual : ∀ A, index -> poor A -> Type;

  down : ∀ A t, rich t A -> poor A;
  down_qual : ∀ A t x, qual A t (down A t x);

  lift : ∀ A t (x : poor A), qual A t x -> rich t A;

  lift_down : ∀ A t x H,
    H = down_qual A t x -> lift A t (down A t x) H = x;
  down_lift : ∀ A t x H, down A t (lift A t x H) = x
}.

Import EqNotations.

Definition to_list `(v : vec A n) : list A.
Proof.
  induction n; simpl in v.
    exact List.nil.
  exact (List.cons (fst v) (IHn (snd v))).
Defined.

Definition of_list `(v : list A) : vec A (length v).
Proof.
  induction v; simpl; intros.
    exact tt.
  exact (a, IHv).
Defined.

Definition of_list_n `(v : list A) (n : nat) : option (vec A n).
Proof.
  generalize dependent v.
  induction n; simpl; intros.
    destruct v.
      exact (Some tt).
    exact None.
  destruct v; simpl.
    exact None.
  destruct (IHn v).
    exact (Some (a, v0)).
  exact None.
Defined.

Definition of_list_H `(v : list A) (n : nat) : length v = n -> vec A n.
Proof.
  generalize dependent v.
  induction n; simpl; intros.
    destruct v.
      exact tt.
    inversion H.
  destruct v; simpl.
    inversion H.
  exact (a, IHn v (eq_add_S _ _ H)).
Defined.

Lemma of_list_n_to_list (A : Type) (n : nat) (v : vec A n) :
  of_list_n (to_list v) n = Some v.
Proof.
  induction n; simpl; destruct v; auto; simpl.
  now rewrite IHn.
Defined.

Lemma length_to_list {A : Type} {n : nat} (v : vec A n) :
  length (to_list v) = n.
Proof. induction n; simpl; auto. Defined.

Lemma of_list_to_list (A : Type) (n : nat) (v : vec A n) :
  forall H : length (to_list v) = n, of_list_H (to_list v) n H = v.
Proof.
  induction n; destruct v; auto; intros.
  simpl in H.
  specialize (IHn _ (eq_add_S _ _ H)).
  simpl.
  now rewrite IHn.
Defined.

Lemma to_list_of_list (A : Type) (n : nat) (v : list A) :
  forall H : length v = n, to_list (of_list_H v n H) = v.
Proof.
  intros.
  generalize dependent v.
  induction n; destruct v; auto; intros; inversion H.
  subst.
  specialize (IHn _ (eq_add_S _ _ H)).
  simpl.
  now rewrite IHn.
Defined.

Program Instance lists_and_vectors :
  Reflected nat (fun n A => vec A n) list := {
  qual  := fun _ n xs => length xs = n;
  down  := fun _ _ => to_list;
  lift  := fun _ n l => of_list_H l n
}.
Next Obligation. apply length_to_list. Defined.
Next Obligation. apply of_list_to_list. Defined.
Next Obligation. apply to_list_of_list. Defined.

Inductive RMorph : Type -> Type -> Type :=
  | RNth A (n : nat) : RMorph (vector A n * Fin.t n) A
  | RFunc A B : (A -> B) -> RMorph A B.

Fixpoint rmorphD `(f : RMorph A B) : A -> B :=
  match f with
  | RNth A n => fun '(v, i) => v[@i]
  | RFunc A B f => f
  end.

Program Definition R : Category := {|
  obj := Coq;
  hom := RMorph;
  homset := fun x y =>
    {| equiv := fun f g => ∀ x, rmorphD f x = rmorphD g x |};
  id := fun x => RFunc x x id;
  compose := fun _ _ _ f g => RFunc _ _ (rmorphD f \o rmorphD g)
|}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation.
  proper.
  now rewrite H0, H.
Qed.

Inductive WMorph : Type -> Type -> Type :=
  | WNth A : WMorph (list A * nat) (option A)
  | WFunc A B : (A -> B) -> WMorph A B.

Fixpoint wmorphD `(f : WMorph A B) : A -> B :=
  match f with
  | WNth A => fun '(v, i) => List.nth_error v i
  | WFunc A B f => f
  end.

Program Definition W : Category := {|
  obj := Coq;
  hom := WMorph;
  homset := fun x y =>
    {| equiv := fun f g => ∀ x, wmorphD f x = wmorphD g x |};
  id := fun x => WFunc x x id;
  compose := fun _ _ _ f g => WFunc _ _ (wmorphD f \o wmorphD g)
|}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation.
  proper.
  now rewrite H0, H.
Qed.

Program Definition WSub : Subcategory W := {|
  sobj := fun _ => True;
  shom := fun x y ox oy (f : x ~> y) =>
    match f in WMorph x' y' return x = x' -> y = y' -> Type with
    | WNth A => fun H1 H2 => _
    | WFunc A B x => fun _ _ => True
    end eq_refl eq_refl
|}.

Program Definition W : Category := Sub _ WSub.

Lemma W_Full : Full _ WSub.
Proof. construct. Qed.

Lemma W_Replete : Replete _ WSub.
Proof. construct; construct; construct. Qed.

Lemma W_Wide : Wide _ WSub.
Proof. construct. Qed.

Definition forget_mor `(x : RMorph A B f) : ∃ A' B' f', WMorph A' B' f'.
Proof.
  induction x.
  - exists (list A * nat)%type, (option A).
    exists (fun '(v, i) => List.nth_error v i).
    apply WNth.
  - exists A.
    exists B.
    exists f.
    apply WFunc.
Defined.

Program Instance Forget : R ⟶ W := {
  fobj := fun x => x;
  fmap := fun x y f => _
}.
Next Obligation.
  induction X.
  - pose (@forget_mor (vector A n ∧ Fin.t n) A
                      (fun '(v, i) => Vector.nth v i)
                      (RNth A n)).
    exists (fun '(v, i) => Vector.nth v i).
    destruct s, s, s.

Lemma there_exists (i : nat) A (l : list A) :
  i < length l ->
  ∃ x, List.nth_error l i = Some x.
Proof.
  intros.
  rewrite <- (@down_lift _ _ _ lists_and_vectors _ (length l) l eq_refl).
  eexists.
  clear H.
  dependent destruction (length l).
  simpl in v.
