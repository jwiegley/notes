Require Import
  Coq.Arith.Arith
  Coq.QArith.QArith
  Coq.Classes.Equivalence
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Init.Logic
  Coq.Program.Program
  Coq.Sets.Ensembles
  Coq.Reals.Reals
  Coq.Reals.RIneq
  Coq.micromega.Lra
  Psatz.

Open Scope R_scope.

Generalizable All Variables.

Theorem Rmul_div_distr n m o : o <> 0 -> n * (m / o) = (n * m) / o.
Proof. intros; now field. Qed.

Theorem Rmul_div n m : n <> 0 -> n * (m / n) = m.
Proof. intros; now field. Qed.

Theorem Rdiv_mul n m : n <> 0 -> n * m / n = m.
Proof. intros; now field. Qed.

Theorem Rdiv_mul_den n m : n <> 0 -> m <> 0 -> n / (m * n) = 1 / m.
Proof. intros; now field. Qed.

Theorem Rdiv_0 n : n <> 0 -> 0 / n = 0.
Proof. intros; now field. Qed.

Theorem Rdiv_n n : n <> 0 -> n / n = 1.
Proof. intros; now field. Qed.

Theorem Rdiv_mul_inv n m : m <> 0 -> n / m = n * / m.
Proof. intros; now field. Qed.

Theorem Rmult_mono_le n m o : 0 < o -> m / o <= n / o -> m <= n.
Proof.
  intros.
  apply Rmult_le_reg_r with (r := / o).
    now apply Rinv_0_lt_compat.
  rewrite <- !Rdiv_mul_inv; lra.
Qed.

Theorem Rlt_div n m o : m > 0 -> n / m < o / m <-> n < o.
Proof.
  intros H; split; intros; pose proof (Rinv_0_lt_compat _ H); nra.
Qed.

Theorem Rlt_plus n m o : n + m < o + m <-> n < o.
Proof. split; nra. Qed.
