Require Import Coq.ZArith.ZArith. (* integers *)
Require Import Coq.Lists.List.    (* lists *)
Require Import Coq.Lists.ListDec.
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Le.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Bool.Sumbool.
Require Import Bool.Bool.
Import ListNotations.
Section Count.

  Variable cand : Type.
  Variable cand_all : list cand.
  Hypothesis dec_cand : forall n m : cand, {n = m} + {n <> m}.
  Hypothesis cand_fin : forall c : cand, In c cand_all.
  (* Variable wins:  cand -> (cand -> cand -> Z) -> Type.
  Variable loses: cand -> (cand -> cand -> Z) -> Type.*)
  Definition ballot := cand -> nat.
  Definition ballot_valid (p : ballot) : Prop :=
    forall c : cand, p c > 0.
 
  Lemma valid_or_invalid_ballot : forall b : ballot, {ballot_valid b} + {~ballot_valid b}.
  Proof.
    unfold ballot_valid; intro.
    revert cand_fin.
    cut ({(forall c, In c cand_all -> b c > 0)} +
         {~ (forall c, In c cand_all -> b c > 0)}).
      intros.
      destruct H; intuition.
    induction cand_all as [|? ? [?|?]]; intuition; [firstorder|].
    destruct (le_gt_dec (b a) 0).
      right; intro.
      destruct (H a (or_introl eq_refl)); intuition.
    left; intros.
    destruct H; auto; congruence.
  Qed.
End Count.
