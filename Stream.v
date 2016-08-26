Require Import Fiat.ADT Fiat.ADTNotation.
Require Import Coq.Sets.Ensembles.
Require Import Omega.

(* A stream is a series of values at ordered positions. *)
Definition Stream (A : Type) := nat -> Comp A.

(* A bistream is a stream that includes communication with upstream. *)
Definition Bistream (A' A : Type) := nat -> A' -> Comp A.

(* A pipe connects two bi-directional streams and produces a result after a
   certain number of steps. *)
Definition Pipe (A' A B' B R : Type) :=
  Bistream A' A -> Bistream B B' -> nat -> Comp R.

Notation "()" := (unit : Type).

Definition Void := False.

Definition Effect := Pipe Void () () Void.

Definition runEffect {R} (p : Effect R) : Comp R :=
  p (fun _ _ => ret tt) (fun _ _ => ret tt) 0.

Definition Producer B := Pipe Void () () B.

Definition Producer' B R := forall {X' X}, Pipe X' X () B R.

Definition yield {X' X A} (x : A) : Pipe X' X () A () :=
  fun _inc out pos =>
    v <- out 0 x;
    { res | res = v /\ pos = 0 }.

Definition forP `(p : Pipe x' x b' b a') `(f : b -> Pipe x' x c' c b') :
  Pipe x' x c' c a' :=
  fun inc out =>
    p inc (fun pos b => f b inc out pos).

Require Import FunctionalExtensionality.

Theorem for_yield_f `(f : b -> Pipe x' x c' c ()) z :
  forP (yield z) f = f z.
Proof.
  unfold forP.
  extensionality inc.
  extensionality out.
  unfold yield.
  extensionality pos.
  induction pos; simpl.
    apply Extensionality_Ensembles;
    split; intros;
    intros ??.
      do 2 destruct H.
      unfold Ensembles.In in *.
      destruct H0; subst.
      assumption.
    eexists; split.
      exact H.
    constructor; auto.
  apply Extensionality_Ensembles;
  split; intros;
  intros ??.
    do 2 destruct H.
    unfold Ensembles.In in *.
    destruct H0; subst.
    discriminate.
  - eexists; simpl;
    unfold Ensembles.In in *.
      exact H.
    constructor; auto.
Admitted.

Theorem for_yield `(s : Pipe x' x () b ()) : forP s yield = s.
Proof.
  unfold forP.
  extensionality inc.
  extensionality out.
  unfold yield; simpl.
  extensionality pos.
Admitted.