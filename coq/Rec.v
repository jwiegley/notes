Require Import Coq.Setoids.Setoid.
Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.

Generalizable All Variables.

Set Universe Polymorphism.

Inductive listF (A r : Type) : Type :=
  | Nil
  | Cons : A -> r -> listF A r.

Arguments Nil {_ _}.
Arguments Cons {_ _} _ _.

Definition listF_map {T A B} (f : A -> B) (x : listF T A) : listF T B :=
  match x with
  | Nil => Nil
  | Cons x r => Cons x (f r)
  end.

Program Instance List {A : Type} : Coq ⟶ Coq := {
  fobj := listF A;
  fmap := @listF_map A
}.
Next Obligation.
  proper.
  unfold listF_map.
  destruct x1; auto.
  f_equal.
  apply H.
Qed.
Next Obligation. destruct x0; auto. Qed.
Next Obligation. destruct x0; auto. Qed.

Inductive Fix (f : Type -> Type) : Type :=
| mkFix : forall x, f x -> (x -> Fix f) -> Fix f.

Arguments mkFix {f x} _ _.

Definition list (A : Type) := Fix (listF A).

Fixpoint cata {F : Coq ⟶ Coq} {A} (alg : F A -> A) (xs : Fix F) : A :=
  match xs with
  | mkFix x k => alg (fmap[F] (fun t => cata alg (k t)) x)
  end.

Definition app {A} (xs ys : list A) : list A :=
  let phi (x : List (list A)) : list A :=
      match x with
      | Nil => ys
      | Cons x r => mkFix (Cons x r) (fun r => ys)
      end in
  cata phi xs.

Fixpoint app {A} (xs ys : list A) : list A :=
  match xs with
  | mkFix Nil _  => ys
  | mkFix (Cons x r) k  => mkFix (Cons x r) (fun r => app (k r) ys)
  end.

Infix "++" := app (at level 60, right associativity).

Lemma app_assoc {A} (xs ys zs : list A) :
  (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
  induction xs.
  simpl.
  destruct f; auto.
  simpl.
  f_equal.
  setoid_rewrite H.