Require Import Program.
(* Require Import FunctionalExtensionality. *)
Require Import Coq.Lists.List.
Require Import Coq.Classes.Equivalence.

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.

Section LTL.

Variable a : Type.
Variable b : Type.

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom
  | Query (v : a -> b -> Prop)
  | Not (p : LTL)
  | And (p q : LTL)
  | Or (p q : LTL)
  | Impl (p q : LTL)

  (* Temporal layer *)
  | Next (p : LTL)
  | Eventually (p : LTL)
  | Until (p q : LTL)
  | Always (p : LTL).

Notation "⊤" := Top (at level 50).
Notation "⊥" := Bottom (at level 50).
Notation "¬ x" := (Not x) (at level 50).
Infix "∧" := And (at level 50).
Infix "∨" := Or (at level 50).
Infix "→" := Impl (at level 50).
Notation "'X' x" := (Next x) (at level 50).
Notation "◇ x" := (Eventually x) (at level 50).
(* Notation "'F' x" := (Eventually x) (at level 50). *)
Notation "p 'U' q" := (Until p q) (at level 50).
Notation "□ x" := (Always x) (at level 50).
(* Notation "'G' x" := (Always x) (at level 50). *)

Fixpoint LTL_size (p : LTL) : nat :=
  match p with
  | Query v      => 1
  | Top          => 1
  | Bottom       => 1
  | Not p        => 1 + LTL_size p
  | And p q      => 1 + LTL_size p + LTL_size q
  | Or p q       => 1 + LTL_size p + LTL_size q
  | Impl p q     => 1 + LTL_size p + LTL_size q
  | Next p       => 1 + LTL_size p
  | Eventually p => 1 + LTL_size p
  | Until p q    => 1 + LTL_size p + LTL_size q
  | Always p     => 1 + LTL_size p
  end.

Definition remaining (s : Stream) (p : LTL) := length s + LTL_size p.

(* The [term] proposition must hold for any dangling cases, such as
   [EndOfTrace] and [UntilSing]. Choosing [term] to be [False] has the effect
   of requiring all matching formula to match some prefix of the input
   completely. *)
Inductive Witness {term : Prop} : Stream -> LTL -> Prop :=
  | EndOfTrace     : forall (t : term) p, p <> Top -> Witness [] p
  | IsTrue         : forall xs, Witness xs Top
  | Base           : forall (q : a -> b -> Prop) x xs w,
      q x w -> Witness (x :: xs) (Query q)
  | Negated        : forall p xs,
      (Witness xs p -> False) -> Witness xs (¬p)
  | Both           : forall p q xs,
      Witness xs p -> Witness xs q -> Witness xs (p ∧ q)
  | InLeft         : forall p q xs,
      Witness xs p -> Witness xs (p ∨ q)
  | InRight        : forall p q xs,
      Witness xs q -> Witness xs (p ∨ q)
  (* | Implied           : forall p q xs, *)
  (*     (Witness xs p -> Witness xs q) -> Witness xs (p → q) *)
  | NextFwd        : forall p x xs,
      Witness xs p -> Witness (x :: xs) (X p)
  | EventuallyStop : forall p xs,
      Witness xs p -> Witness xs (◇ p)
  | EventuallyFwd  : forall p x xs,
      Witness xs (◇ p) -> Witness (x :: xs) (◇ p)
  | UntilNil       : forall p q xs,
      Witness xs q -> Witness xs (p U q)
  | UntilCons      : forall p q x xs,
      Witness (x :: xs) p -> Witness xs (p U q) -> Witness (x :: xs) (p U q)
  | UntilSing      : forall (t : term) p q x,
      Witness [x] p -> Witness [x] (p U q)
  | AlwaysCons     : forall p ps x xs,
      Witness (x :: xs) p -> Witness xs (□ ps) -> Witness (x :: xs) (□ p)
  | AlwaysSing     : forall p x,
      Witness [x] p -> Witness [x] (□ p).

(* Strong Interpretation, where an EndOfTrace is not considered a match. *)
Notation "T ⊢ L" := (Witness T L) (at level 70).

(* Weak Interpretation, where an EndOfTrace is considered a match. *)
Notation "T ⊢~ L" := (@Witness True T L) (at level 70).

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition ltl_equiv (p q : LTL) : Prop :=
  forall t s, @Witness t s p <-> @Witness t s q.

Program Instance Equivalence_ltl_equiv : Equivalence ltl_equiv.
Next Obligation.
  repeat intro; split; auto.
Qed.
Next Obligation.
  repeat intro; intros.
  now symmetry.
Qed.
Next Obligation.
  repeat intro; intros.
  specialize (H t s).
  specialize (H0 t s).
  now rewrite H, H0.
Qed.

Definition ltl_strong_equiv (p q : LTL) : Prop :=
  forall s, @Witness False s p <-> @Witness False s q.

Infix "≈" := equiv (at level 90).

Program Instance Equivalence_ltl_strong_equiv : Equivalence ltl_strong_equiv | 9.
Next Obligation.
  repeat intro; split; auto.
Qed.
Next Obligation.
  repeat intro; intros.
  now symmetry.
Qed.
Next Obligation.
  repeat intro; intros.
  specialize (H s).
  specialize (H0 s).
  now rewrite H, H0.
Qed.

Infix "≈[strong]" := ltl_strong_equiv (at level 90).

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof.
  repeat intro; split; intros.
  - induction s.
      inversion_clear H.
        now constructor.
      now apply UntilNil.
    inversion_clear H.
      now constructor.
    apply UntilCons; auto.
    now constructor.
  - induction s; intros.
      inversion_clear H.
        now constructor.
      now apply EventuallyStop.
    inversion_clear H.
    + now constructor.
    + now apply EventuallyFwd; auto.
    + apply EventuallyFwd.
      now end_of_trace.
Qed.

Lemma witness_neg s φ : @Witness False s (¬ φ) <-> ~ (@Witness False s φ).
Proof.
  split; repeat intro.
  - inversion_clear H; auto.
    admit.
  - induction s.
    + constructor.
      apply H.
        admit.
      admit.
    + admit.
Abort.

(* ψ always remains true *)
Lemma always_remains_true (ψ : LTL) : □ ψ ≈ ⊥ R ψ.
Proof. Abort.

Lemma always_remains_true' (ψ : LTL) : □ ψ ≈ ¬◇ ¬ψ.
Proof. Abort.

Definition weakUntil (φ ψ : LTL) := (φ U ψ) ∨ □ φ.
Notation "p 'W' q" := (weakUntil p q) (at level 50).

Definition strongRelease (φ ψ : LTL) := ψ U (φ ∧ ψ).
Notation "p 'M' q" := (strongRelease p q) (at level 50).

Lemma foo2 (φ ψ : LTL) : φ W ψ ≈ φ U (ψ ∨ □ φ).
Proof. Abort.

Lemma foo3 (φ ψ : LTL) : φ W ψ ≈ ψ R (ψ ∨ φ).
Proof. Abort.

Lemma foo4 (φ ψ : LTL) : φ U ψ ≈ ◇ ψ ∧ (φ W ψ).
Proof. Abort.

Lemma foo5 (φ ψ : LTL) : φ R ψ ≈ ψ W (ψ ∧ φ).
Proof. Abort.

Lemma foo6 (φ ψ : LTL) : φ M ψ ≈ ¬(¬φ W ¬ψ).
Proof. Abort.

Lemma foo7 (φ ψ : LTL) : φ M ψ ≈ (φ R ψ) ∧ ◇ φ.
Proof. Abort.

Lemma foo8 (φ ψ : LTL) : φ M ψ ≈ φ R (ψ ∧ ◇ φ).
Proof. Abort.

(** Distributivity *)

Lemma foo10 (φ ψ : LTL) : X (φ ∨ ψ) ≈ (X φ) ∨ (X ψ).
Proof. Abort.

Lemma foo11 (φ ψ : LTL) : X (φ ∧ ψ) ≈ (X φ) ∧ (X ψ).
Proof. Abort.

Lemma foo12 (φ ψ : LTL) : X (φ U ψ) ≈ (X φ) U (X ψ).
Proof. Abort.

Lemma foo13 (φ ψ : LTL) : ◇ (φ ∨ ψ) ≈ (◇ φ) ∨ (◇ ψ).
Proof. Abort.

Lemma foo14 (φ ψ : LTL) : □ (φ ∧ ψ) ≈ (□ φ) ∧ (□ ψ).
Proof. Abort.

Lemma foo15 (ρ φ ψ : LTL) : ρ U (φ ∨ ψ) ≈ (ρ U φ) ∨ (ρ U ψ).
Proof. Abort.

Lemma foo16 (ρ φ ψ : LTL) : (φ ∧ ψ) U ρ ≈ (φ U ρ) ∧ (ψ U ρ).
Proof. Abort.

(** Negation propagation *)

Lemma foo18 (φ : LTL) : ¬(X φ) ≈ X ¬φ.
Proof.
  repeat intro; split; intros.
  - induction s.
      inversion_clear H.
        end_of_trace.
    inversion_clear H.
  - induction s; intros.
      inversion_clear H.
        end_of_trace.
    inversion_clear H.

    + now constructor.
    + now apply EventuallyFwd; auto.
    + apply EventuallyFwd.
      now end_of_trace.
Qed.

Lemma foo19 (φ : LTL) : ¬(◇ φ) ≈ □ ¬φ.
Proof. Abort.

Lemma foo20 (φ ψ : LTL) : ¬ (φ U ψ) ≈ (¬φ R ¬ψ).
Proof. Abort.

Lemma foo21 (φ ψ : LTL) : ¬ (φ W ψ) ≈ (¬φ M ¬ψ).
Proof. Abort.

Lemma foo22 (φ : LTL) : ¬(□ φ) ≈ ◇ ¬φ.
Proof. Abort.

Lemma foo23 (φ ψ : LTL) : ¬ (φ R ψ) ≈ (¬φ U ¬ψ).
Proof. Abort.

Lemma foo24 (φ ψ : LTL) : ¬ (φ M ψ) ≈ (¬φ W ¬ψ).
Proof. Abort.

(** Special Temporal properties *)

Lemma foo25 (φ : LTL) :   ◇ φ ≈ ◇ ◇ φ.
Proof. Abort.

Lemma foo26 (φ : LTL) :   □ φ ≈ □ □ φ.
Proof. Abort.

Lemma foo27 (φ ψ : LTL) : φ U ψ ≈ φ U (φ U ψ).
Proof. Abort.

Lemma foo28 (φ ψ : LTL) : φ U ψ ≈ ψ ∨ (φ ∧ X(φ U ψ)).
Proof. Abort.

Lemma foo29 (φ ψ : LTL) : φ W ψ ≈ ψ ∨ (φ ∧ X(φ W ψ)).
Proof. Abort.

Lemma foo30 (φ ψ : LTL) : φ R ψ ≈ ψ ∧ (φ ∨ X(φ R ψ)).
Proof. Abort.

Lemma foo31 (φ : LTL) :   □ φ ≈ φ ∧ X(□ φ).
Proof. Abort.

Lemma foo32 (φ : LTL) :   ◇ φ ≈ φ ∨ X(◇ φ).
Proof. Abort.

End LTL.
