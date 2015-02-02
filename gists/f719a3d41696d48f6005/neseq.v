Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Relations.Relations.

Require Export Ssreflect.choice.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.fintype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section NonEmpty.

Variables (T : eqType).

Inductive neseq : predArgType := Neseq s of 0 < @size T s.

Coercion seq_of_ne i := let: Neseq l _ := i in l.

Fixpoint eqneseq (s1 s2 : neseq) {struct s2} :=
  match s1, s2 with Neseq x1 _, Neseq x2 _ => (x1 == x2) end.

Lemma eqneseqP : Equality.axiom eqneseq.
Proof.
  move. elim=> [s1 p1] [s2 p2] /=.
Admitted.

Canonical neseq_subType := [subType for seq_of_ne].

Canonical neseq_eqMixin := EqMixin eqneseqP.
Canonical neseq_eqType := Eval hnf in EqType neseq neseq_eqMixin.

(* Definition neseq_choiceMixin := [choiceMixin of neseq by <:]. *)
(* Canonical neseq_choiceType := *)
(*   Eval hnf in ChoiceType neseq neseq_choiceMixin. *)

Definition nehead (s : neseq) : T. elim: s; elim=> //. Defined.

Definition nelast (s : neseq) : T.
  elim: s; elim; first by done.
  move=> a l H H'.
  apply: (last a l).
Defined.

End NonEmpty.

Arguments Neseq {T} s p.

Compute nehead (Neseq [:: 1; 2; 3] is_true_true).
Compute nelast (Neseq [:: 1; 2; 3] is_true_true).
Compute size (Neseq [:: 1; 2; 3] is_true_true).
Compute map (addn 1) (Neseq [:: 1; 2; 3] is_true_true).

Import EqNotations.

Lemma nemap_helper {a b : eqType} (f : a -> b) (s : seq a)
  : 0 < size s -> 0 < size [seq f i | i <- s].
Proof. Admitted.

Fixpoint nemap {a b : eqType} (f : a -> b) (ne : neseq a) : neseq b :=
  match ne with
    | Neseq s H => Neseq (map f s) (nemap_helper f H)
  end.

Lemma nemap_spec : forall (a b : eqType) (f : a -> b)
                          (x : a) (s : seq a) (H : 0 < size (x :: s)),
  nemap f (Neseq (x :: s) H) = Neseq (f x :: map f s) H.
Proof. Admitted.

Lemma nemap_head_spec : forall {a b : eqType} (f : a -> b) (xs : neseq a),
  nehead (nemap f xs) = f (nehead xs).
Proof.
  intros. destruct xs; induction s; auto; first by [].
  simpl. rewrite (nemap_spec f i). reflexivity.
Qed.

Lemma nemap_last_spec : forall {a b : eqType} (f : a -> b) (xs : neseq a),
  nelast (nemap f xs) = f (nelast xs).
Proof.
  intros. destruct xs; induction s; auto; first by [].
  rewrite (nemap_spec f i). apply last_map.
Qed.
