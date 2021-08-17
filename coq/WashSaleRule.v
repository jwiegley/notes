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

Theorem Rmax_refl n : Rmax n n = n.
Proof.
  unfold Rmax.
  destruct (Rle_dec _ _); auto.
Qed.

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

Theorem Rdiv_div n m o : m <> 0 -> o <> 0 -> (n / m) / (o / m) = n / o.
Proof. intros; now field. Qed.

Theorem Rdiv_mono_le n m o : 0 < o -> m / o <= n / o <-> m <= n.
Proof.
  intros H; split; intros; pose proof (Rinv_0_lt_compat _ H); nra.
Qed.

Theorem Rdiv_mono_lt n m o : m > 0 -> n / m < o / m <-> n < o.
Proof.
  intros H; split; intros; pose proof (Rinv_0_lt_compat _ H); nra.
Qed.

Theorem Rlt_plus n m o : n + m < o + m <-> n < o.
Proof. split; lra. Qed.

Section WashSaleRule.

Definition Quantity := R.
Definition Price := R.
Definition Date := R.
Definition Days := R.

(** A Ticket is what gets submitted a broker, but doesn't have a "meaning" yet
    until it is known what has occurred in the past. For example, a ticket for
    -100 shares could represent a sale of previously purcased shares, or a new
    short position. *)
Record Ticket := {
  date  : Date;
  count : Quantity;             (* positive for buy, negative for sell *)
  price : Price;                (* price transaction occurred at *)
}.

Record Opening := {
  opening_ticket : Ticket;
  (* When no wash sale is applied, opening_basis = price opening_ticket *)
  opening_basis  : Price;
}.

(** A closing ticket always closes existing open position. However, because
    the ticket may specify a fraction of the total open lots, it also
    specifies the "remainder" that was not addressed by the closing. *)
Record Closing := {
  closing_ticket    : Ticket;
  closing_lots      : list Opening;
  closing_remainder : Opening;
}.

Definition sum (xs : list R) : R := List.fold_left Rplus xs 0.

Definition gainsLosses (c : Closing) : list Price :=
  List.map (fun o => count (opening_ticket o) *
                     (price (closing_ticket c) - opening_basis o))
           (closing_lots c).

Definition gainLoss (c : Closing) : Price := sum (gainsLosses c).

Inductive Transaction :=
  | Open (opening : Opening)
  | Close (closing : Closing).

Inductive WashSale :
  Ensemble Transaction ->        (* previously transacted shares *)
  Transaction     ->             (* lot to be transacted *)
  Transaction     ->             (* adjusted transaction, if opening *)
  Ensemble Transaction ->        (* resulting set of transactions *)
  Prop :=

  (** When a new position is opened, any unapplied wash sale amounts may be
      transferred into the cost basis of that new lot. *)
  | Opened old lot lot' new : WashSale old lot lot' new

  (** When closing a position at a loss, previous openings may have their cost
      basis adjusted by this "wash sale". Unapplied adjustments are remembered
      toward possible future openings. *)
  | ClosedAtLoss old lot lot' new : WashSale old lot lot' new

  (** When closing at break-even or a profit, we have no need to remember this
      lot, we just remove the positions it closes from the set of shares. *)
  | Closed old lot lot' new : WashSale old lot lot' new
.

End WashSaleRule.
