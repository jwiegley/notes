Require Export Ssreflect.ssreflect.
Require Export Ssreflect.ssrfun.
Require Export Ssreflect.ssrbool.
Require Export Ssreflect.eqtype.
Require Export Ssreflect.seq.
Require Export Ssreflect.ssrnat.
Require Export Ssreflect.fintype.

Require Import Coq.Reals.Reals.
(* Require Import Flocq.Core.Fcore. *)

Open Scope R_scope.

Goal (79 / 10) < (80 / 10).
Proof.
  compute.
  apply Rmult_lt_compat_r => //.
    apply: Rinv_0_lt_compat.
    omega_sup.
  omega_sup.
Qed.
