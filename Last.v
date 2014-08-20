Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Set Implicit Arguments.

Require Import List.

Lemma skip_hd A d :
  forall (i : nat) (l : list A),
    hd d (skipn i l) = nth i l d.
Proof.
  by elim=> [ [] | n IH []].
Qed.

Lemma skip_last A d :
  forall (i : nat) (l : list A),
    i < length l ->
    last (skipn i l) d = last l d.
Proof.
  elim=> // n IH [|x [|y l]] // Hlt.
  by rewrite IH.
Qed.

Require Export Coq.Lists.List.

(* Lemma skip_hd: *)
(* forall i: nat, *)
(* forall A: Type, *)
(* forall d: A, *)
(* forall l: list A, *)
(* hd d (skipn i l) = nth i l d. *)
(* Proof. *)
(* intros i A d; induction i; simpl; intros [|h l]; simpl; auto. *)
(* Qed. *)

Fixpoint lt2 (m n : nat) : Prop :=
match n with
| O => False
| S n => match m with O => True | S m => lt2 m n end
end.

(* Lemma lt_to_lt2 (m n : nat) : m < n -> lt2 m n. *)
(* Proof. *)
(* intros H; induction H. *)
(* + induction m; simpl; auto. *)
(* + revert IHle; clear; revert m; induction m0; intros [|x]; simpl; auto. *)
(* intros []. *)
(* Qed. *)

Lemma big_enough : forall {X} n l,
  S n <= length l -> exists (x : X) xs, l = x :: xs.
Proof.
  intros X n l.
  induction l; intros.
    inversion H.
  eauto.
Qed.

Lemma skip_last': forall (i: nat) (A: Type) (d: A) (l: list A),
  i < length l -> last (skipn i l) d = last l d.
Proof.
  intros i A d l.
  generalize dependent i.
  induction l; intros.
    inversion H.
  destruct i; auto.
  simpl in *.
  apply Le.le_S_n in H.
  rewrite IHl.
    apply big_enough in H.
    destruct H. destruct H.
    rewrite H. reflexivity.
  apply H.
Qed.
