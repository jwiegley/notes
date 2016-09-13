Require Import Fiat.Computation.Core.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Cont.
Require Import PeanoNat.

Program Instance State_Monad (S : Type) : Monad (State S) := {
  Return := fun A x => fun s => (x, s);
  Bind   := fun A B m k => fun s => let (a, s') := m s in k a s';
  Equiv  := fun A m1 m2 => forall (s : S), m1 s = m2 s
}.
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.

(* Require Import Coq.Logic.Classical_Prop. *)

Program Instance State_Computable (S : Type) :
  inhabited S -> Computable (State S) := {
  computes_to := fun A m a => exists s s', m s = (a, s')
}.
Obligation 1.
  intros ??????; split; intros; subst;
  destruct H2, H1; exists x0; exists x1;
  rewrite <- H1 || rewrite H1; auto.
Qed.
Obligation 2.
  destruct H.
  exists X; exists X; reflexivity.
Qed.
Obligation 4.
  exists H0.
  exists H2.
  rewrite H5.
Admitted.
Obligation 5.
  destruct (ca H0) eqn:Heqe.
  exists a.
  split; intros.
    exists H0.
    exists s.
    assumption.
  exists s.
  exists H1.
  assumption.
Qed.

Program Instance option_Monad : Monad option := {
  Return := fun A x => Some x;
  Bind   := fun A B m k => match m with
                           | Some x => k x
                           | None => None
                           end;
  Equiv  := fun A m1 m2 => m1 = m2
}.
Obligation 1.
  intros ??????.
  rewrite H.
  destruct y.
    rewrite H0.
    reflexivity.
  reflexivity.
Qed.
Obligation 3.
  destruct x; reflexivity.
Qed.
Obligation 4.
  destruct x; auto.
Qed.

Obligation Tactic := simpl; intros; auto.

Program Instance option_Computable : Computable option := {
  computes_to := fun A m a => m = Some a
}.
Obligation 2.
  inversion H; auto.
Qed.
Obligation 3.
  rewrite H.
  assumption.
Qed.
Obligation 4.
  destruct ca.
    exists a; auto.
  discriminate.
Qed.

Program Instance Cont_Monad (R : Type) : Monad (Cont R) := {
  Return := fun A x => fun k => k x;
  Bind   := fun A B m f => fun k => m (fun a => f a k);
  Equiv  := fun A m1 m2 => forall k, m1 k = m2 k
}.
Obligation 1.
  repeat constructor.
    intros x y H k.
    symmetry.
    intuition.
  intros x y z H1 H2 k.
  transitivity (y k); intuition.
Qed.
Obligation 2.
  intros ?????? k.
  rewrite H.
  f_equal.
  Require Import FunctionalExtensionality.
  extensionality a.
  apply H0.
Qed.

Program Instance Cont_Computable :
  inhabited R -> Computable (fun A => forall R, Cont R A) := {
  computes_to := fun A m a => m _ id = a
}.
Obligation 1.
  intros ??????; split; intros.
Admitted.
Obligation 2.
  destruct H.
  exists (fun _ => X).
  reflexivity.
Qed.
Obligation 3.
  destruct H0.
  
Obligation 4.
  destruct ca.
    exists a; auto.
  discriminate.
Qed.

Definition foo (x : nat) : State nat nat :=
  y <- get;
  if y <? 10
  then ret 10
  else ret 50.

Lemma refine_stateful :
  { f : nat -> State nat nat
  & forall x : nat, refine (foo x) (f x) }.
Proof.
  exists (fun x =>
            y <- get;
            if 10 <=? y
            then ret 50
            else ret 10).
  unfold foo; intros ???.
  reduce_computation.
    destruct (10 <? v0) eqn:Heqe; simpl in *;
    exact H.
  destruct (10 <=? v0) eqn:Heqe; simpl in *;
  destruct (v0 <? 10) eqn:Heqe1; simpl in *; auto.
  - Require Import Omega.
    apply Nat.ltb_lt in Heqe1.
    do 10 (destruct v0; try discriminate).
    omega.
  - Require Import Omega.
    apply Nat.ltb_ge in Heqe1.
    do 10 (destruct v0; try omega).
    discriminate.
Qed.
