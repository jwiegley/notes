Require Import Coq.Lists.List.

Generalizable All Variables.

Inductive Listed (A : Type) :=
  | Nil
  | Cons (x : A) (xs : Listed A)
  | App (xs ys : Listed A).

Import ListNotations.

Definition foo {A} (xs ys : list A) := xs ++ ys.

Fixpoint embed {A} (xs : list A) : Listed A :=
  match xs with
  | nil => Nil A
  | cons x xs => Cons A x (embed xs)
  end.

Fixpoint retract {A} (xs : Listed A) : list A :=
  match xs with
  | Nil _ => nil
  | Cons _ x xs => cons x (retract xs)
  | App _ xs ys => retract xs ++ retract ys
  end.

Lemma retract_embed {A} (xs : list A) :
  retract (embed xs) = xs.
Proof. induction xs; simpl; auto; now rewrite IHxs. Qed.

Definition Listed_AbsR {A} (o : list A) (n : Listed A) : Prop :=
  o = retract n.

Lemma foo_listed {A : Type} :
  { f : Listed A -> Listed A -> Listed A
  & forall xs xs' ys ys',
      Listed_AbsR xs xs' ->
      Listed_AbsR ys ys' ->
      Listed_AbsR (foo xs ys) (f xs' ys') }.
Proof.
  eexists.
  unfold Listed_AbsR, foo; simpl; intros; subst.
  now instantiate (1 := @App A); simpl.
Defined.

Eval simpl in (projT1 foo_listed).
