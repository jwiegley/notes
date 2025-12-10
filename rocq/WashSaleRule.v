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

Record Opened := {
  opened_ticket : Ticket;
  (* When no wash sale is applied, opened_basis = price opened_ticket *)
  opened_basis  : Price;
}.

(** A closed ticket always closes existing open position. However, because
    the ticket may specify a fraction of the total open lots, it also
    specifies the "remainder" that was not addressed by the closed. *)
Record Closed := {
  closed_ticket : Ticket;
  closed_lots   : list Opened;
}.

Definition sum (xs : list R) : R := List.fold_left Rplus xs 0.

Definition sumOf {A : Type} (f : A -> R) (xs : list A) : R :=
  sum (List.map f xs).

Theorem sumOf_cons A (f : A -> R) x xs :
  sumOf f (cons x xs) = f x + sumOf f xs.
Proof.
  unfold sumOf, sum; simpl.
  rewrite Rplus_0_l.
  generalize (f x).
  induction xs; simpl; intros; [lra|].
  rewrite Rplus_0_l.
  rewrite IHxs.
  rewrite Rplus_assoc.
  f_equal.
  symmetry.
  apply IHxs.
Qed.

Definition gainsLosses (c : Closed) : list Price :=
  List.map (fun o => count (opened_ticket o) *
                     (price (closed_ticket c) - opened_basis o))
           (closed_lots c).

Definition gainLoss (c : Closed) : Price := sum (gainsLosses c).

Definition FromOption `(mx : option A) : Ensemble A := fun x =>
  match mx with
  | None => False
  | Some x' => x = x'
  end.

Definition FromList `(xs : list A) : Ensemble A := fun x => List.In x xs.

Inductive These (A B : Type) : Type :=
  | This : A -> These A B
  | That : B -> These A B
  | Both : A -> B -> These A B.

Arguments This {A B} _.
Arguments That {A B} _.
Arguments Both {A B} _ _.

(** This inductive proposition determines only what the annotated ticket shall
    be when considering a new ticket against a previous set of transactions.
    We determine how that set of transactions is modified by this ticket using
    a different proposition, for the sake of expositional clarity. *)
Inductive TicketApplied (o : Ensemble Opened) (t : Ticket) :
  These Opened Closed -> Prop :=
  (** In the simplest scenario, this ticket does not relate to any prior
      transaction, and thus represents a new opening of a long or short
      position. *)
  | Open :
      TicketApplied o t (This {| opened_ticket := t; opened_basis := price t |})
  | Close lots :
      (* Using the FIFO method (jww (2021-08-21): we need to support all
         methods), the lots we are closing must be "earliest" in the set. *)
      (forall x y, List.In x lots -> ~ (List.In y lots) -> In _ o y ->
                   date (opened_ticket y) >= date (opened_ticket x)) ->
      sumOf (count ∘ opened_ticket) lots = count t ->
      TicketApplied o t (That {| closed_ticket := t; closed_lots := lots |})
  | OpenAndClose :
      TicketApplied o t (Both {| opened_ticket := t; opened_basis := price t |}
                              {| closed_ticket := t; closed_lots := nil |}).

(** A ticket is determined to be either an opening of a new position, or a
    closing of an old position, or both, depending on the current set of known
    open transactions.

    If it closes a position, the resulting set will be smaller; if it opens a
    new position, the resulting set will be larger. If both, it may be the
    same size, but the contents will have been changed, so the resulting set
    is always different in some way from the input set. *)
Definition applyTicket (opened : Ensemble Opened) (t : Ticket) :
  Ensemble Opened * These Opened Closed :=
  (opened, This {| opened_ticket := t; opened_basis := price t |}).

(** When a transaction is closed at a loss, it may affect the set of both
    known open and closed transactions. It may affect open transactions by
    adjusting their cost basis in order to "apply the wash sale rule"; if may
    affect closed transactions by recording the losing sale in order to apply
    the wash sale rule to future opening transactions. *)

Definition applyClosed
           (opened : Ensemble Opened)
           (closed : Ensemble Closed) (c : Closed) :
  Ensemble Opened * Ensemble Closed :=
  (opened, closed).

Definition washOpened (opens : Ensemble Closed) (t : Ticket) :
  Ensemble Opened * These Opened Closed :=
  (opens, This {| opened_ticket := t; opened_basis := price t |}).

(** When a ticket is submitted to a broker, it can result in both opened and
    closed transaction, and may affect the set of recorded transactions. *)
Inductive Transaction :
  Ensemble Opened     ->       (* previously transacted shares *)
  Ensemble Closed     ->       (* previously transacted shares *)
  Ticket              ->       (* lot to be transacted *)
  Ensemble Opened     ->       (* resulting set of transactions *)
  Ensemble Closed     ->       (* resulting set of transactions *)
  These Opened Closed ->       (* adjusted transaction, if opened *)
  Prop :=

  (** Closed a position at a gain only removes past open positions from the
      set of known transactions.

      jww (2021-08-17): Account for the fact that selling N shares may
      resulting in selling L lots, some of which incur a loss while others
      provide a gain. *)
  | CapitalGain opens closes t xacts :
      Transaction opens closes t
                  (Union _ (Setminus _ old (FromList (List.map Open (closed_lots c))))
                         (FromOption (option_map Open (closed_remainder c))))
                  closes
                  xacts

  (** When a new position is opened, any unapplied wash sale amounts may be
      transferred into the cost basis of that new lot. *)
  | Opened old lot lot' new : WashSale old lot lot' new

  (** When closed a position at a loss, previous openings may have their cost
      basis adjusted by this "wash sale". Unapplied adjustments are remembered
      toward possible future openings. *)
  | ClosedAtLoss old lot lot' new : WashSale old lot lot' new

  (** When closed at break-even or a profit, we have no need to remember this
      lot, we just remove the positions it closes from the set of shares. *)
  | Closed old lot lot' new : WashSale old lot lot' new
.

End WashSaleRule.
