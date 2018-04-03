Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Import VectorNotations.

Generalizable All Variables.

Open Scope nat_scope.

Program Instance fins_nats {n} :
  Fin.t n ≅ { i : nat | i < n } := {
  to := Fin.to_nat;
  from := fun _ => Fin.of_nat_lt _;
  iso_to_from := _;
  iso_from_to := _;
}.
Next Obligation.
  intros.
  unfold fins_nats_obligation_2.
  unfold fins_nats_obligation_1.
  destruct x; simpl.
  apply Fin.to_nat_of_nat.
Qed.
Next Obligation.
  intros.
  unfold fins_nats_obligation_2.
  unfold fins_nats_obligation_1.
  apply Fin.of_nat_to_nat_inv.
Qed.

(** This style of vector allows us to just induct on [nat]. *)
Fixpoint vec (A : Type) (n : nat) : Type :=
  match n with
  | O => unit : Type
  | S x => (A * vec A x)%type
  end.

Definition to_list `(v : vec A n) : { l : list A | length l = n }.
Proof.
  induction n; simpl in v.
    now exists List.nil.
  destruct (IHn (snd v)); clear IHn.
  exists (List.cons (fst v) x); simpl.
  now f_equal.
Defined.

Definition of_list `(v : { l : list A | length l = n }) : vec A n.
Proof.
  intros.
  destruct v.
  generalize dependent n.
  induction x; simpl; intros.
    destruct n; simpl in e.
      exact tt.
    discriminate.
  destruct n; simpl in e.
    discriminate.
  inversion e.
  split.
    exact a.
  apply IHx.
  reflexivity.
Defined.

Lemma to_list_of_list `(v : { l : list A | length l = n }) :
  to_list (of_list v) = v.
Proof.
  destruct v.
  generalize dependent x.
  induction n; intros.
    destruct x.
      simpl.
      f_equal.
      dependent elimination e.
      reflexivity.
    discriminate.
  destruct x.
    discriminate.
  simpl in e.
  inversion e.
  specialize (IHn _ H0).
  destruct e.
  replace (of_list (exist (λ l : list A, length l = S (length x)) (a :: x)%list eq_refl))
     with (a, of_list (exist (λ l : list A, length l = length x) x eq_refl)) by auto.
  subst.
  remember (of_list _) as l.
  simpl; subst.
  rewrite IHn.
  reflexivity.
Qed.

Lemma of_list_to_list `(v : vec A n) :
  of_list (to_list v) = v.
Proof.
  induction n; destruct v; simpl; auto.
  specialize (IHn v).
  destruct (to_list v).
  destruct e.
  simpl.
  f_equal.
  apply IHn.
Qed.

Program Instance vectors_lists {A n} :
  vec A n ≅ { l : list A | length l = n } := {
  to := to_list;
  from := of_list;
  iso_to_from := to_list_of_list;
  iso_from_to := of_list_to_list;
}.

Definition nth_algebra
           `(x : () + (A * (nat -> option A)))
           (i : nat) : option A :=
  match x with
  | Datatypes.inl x => None
  | Datatypes.inr (x, k) =>
    match i with
    | O => Some x
    | S x => k (pred i)
    end
  end.

Fixpoint nth `(l : list A) : nat -> option A :=
  match l with
  | Datatypes.nil       => nth_algebra (Datatypes.inl tt)
  | Datatypes.cons x xs => nth_algebra (Datatypes.inr (x, nth xs))
  end.

Import EqNotations.

Definition vnth_algebra {n : nat}
           `(x : (A * (Fin.t n -> A)))
           (i : Fin.t (S n)) : A :=
  match x with
  | (x, k) =>
    match i in Fin.t (S n') return n = n' -> A with
    | Fin.F1 => fun _ => x
    | Fin.FS n => fun H => k (rew <- H in n)
    end eq_refl
  end.

Definition vnth `(l : vec A n) : Fin.t n -> A.
Proof.
  induction n.
    intros.
    inversion H.
  apply vnth_algebra.
  destruct l.
  exact (a, IHn v).
Defined.

(* We can implement a predicated variant of nth directly by appealing to the
   vector isomorphism. *)
Definition nthH `(l : list A) (i : nat) (H : i < length l) : A :=
  vnth (from vectors_lists (exist _ l eq_refl))
       (from fins_nats (exist _ i H)).

Lemma nth_vnth n A (l : list A) (H : n < length l) :
  nth l n = Some (vnth (from vectors_lists (exist _ l eq_refl))
                       (from fins_nats (exist _ n H))).
Proof.
  generalize dependent n.
  induction l; simpl; intros.
    inversion H.
  destruct n; simpl in *; auto.
  now rewrite <- IHl.
Qed.

Require Coq.omega.Omega.

Lemma rev_nth :
  ∀ (A : Type) (l : list A) (d : A) (n : nat),
  n < length l → nth (rev l) n = nth l (length l - S n).
Proof.
  intros.
  assert (n < length (rev l)) by now rewrite rev_length.
  assert (length l - S n < length l) by Omega.omega.
  rewrite nth_vnth with (H:=H0).
  rewrite nth_vnth with (H:=H1).
  clear.
  apply f_equal.
  (* The indices to nat_rect on both sides are effectively the same: length l
     and length (rev l), however dependent typing prevents us from rewriting
     to do the induction on nat. *)
  Fail rewrite rev_length with (A:=A).
  (* jww (2018-04-03): What to do now? *)
Abort.