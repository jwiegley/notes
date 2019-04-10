Require Import Program.
(* Require Import FunctionalExtensionality. *)
Require Import Coq.Lists.List.
Require Import Coq.Classes.Equivalence.
Require Import Coq.omega.Omega.

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.
Set Transparent Obligations.

Section LTL.

Variable a : Type.
Variable b : Type.

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom
  | Query (v : a -> b -> Prop)
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
Notation "¬ x" := (Impl x Bottom) (at level 50).
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
Inductive Witness {term : Type} : Type :=
  | EndOfTrace (t : term) (l : LTL)
  | IsTrue
  | Base (x : a) (w : b)
  | Both (p q : Witness)
  | InLeft (p : Witness)
  | InRight (q : Witness)
  | Implied (p q : Witness)
  | NextFwd (p : Witness)
  | EventuallyStop (p : Witness)
  | EventuallyFwd (p : Witness)
  | UntilPrf (ps : list Witness) (q : Witness)
  | AlwaysPrf (ps : list Witness).

Fixpoint summation (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | x :: xs' => x + summation xs'
  end.

Lemma S_summation xs : S (summation xs) = summation (1 :: xs).
Proof. induction xs; simpl; auto. Qed.

Lemma plus_summation x xs : x + summation xs = summation (x :: xs).
Proof. induction xs; simpl; auto. Qed.

Lemma summation_plus x xs : summation xs + x = summation (x :: xs).
Proof.
  induction xs; simpl; auto.
  rewrite <- plus_assoc.
  rewrite IHxs.
  simpl.
  rewrite! plus_assoc.
  rewrite (plus_comm a0).
  reflexivity.
Qed.

Fixpoint Witness_size `(p : @Witness term) : nat :=
  match p with
  | EndOfTrace t l => 1 + LTL_size l
  | IsTrue => 1
  | Base x w => 1
  | Both p q => 1 + Witness_size p + Witness_size q
  | InLeft p => 1 + Witness_size p
  | InRight q => 1 + Witness_size q
  | Implied p q => 1 + Witness_size p + Witness_size q
  | NextFwd p => 1 + Witness_size p
  | EventuallyStop p => 1 + Witness_size p
  | EventuallyFwd p => 1 + Witness_size p
  | UntilPrf ps q => 1 + summation (map Witness_size ps) + Witness_size q
  | AlwaysPrf ps => 1 + summation (map Witness_size ps)
  end.

Lemma Witness_not_empty `(p : @Witness term) : Witness_size p > 0.
Proof. induction p; simpl; omega. Qed.

Local Obligation Tactic := program_simpl; simpl; try omega.

(* The [term] proposition must hold for any dangling cases, such as
   [EndOfTrace] and [UntilSing]. Choosing [term] to be [False] has the effect
   of requiring all matching formula to match some prefix of the input
   completely. *)
Program Fixpoint Verify {term : Prop}
        (T : Stream) (L : LTL) (W : @Witness term)
        {measure (Witness_size W)} : Prop :=
  match W with
  | EndOfTrace t l   => l = L /\ L <> ⊤
  | IsTrue           => L = ⊤
  | Base x w         => forall   q, L = Query q -> forall x xs, T = x :: xs -> q x w
  | Both P Q         => forall p q, L = p ∧ q -> Verify T p P /\ Verify T q Q
  | InLeft P         => forall p q, L = p ∨ q -> Verify T p P
  | InRight Q        => forall p q, L = p ∨ q -> Verify T q Q
  | Implied P Q      => forall p q, L = p → q -> Verify T p P -> Verify T q Q
  | NextFwd P        => forall x xs, T = x :: xs -> forall p, L = X p -> Verify xs p P
  | EventuallyStop P => forall p, L = ◇ p -> Verify T p P
  | EventuallyFwd P  => forall x xs, T = x :: xs -> Verify xs L P

  | UntilPrf PS Q    => forall p q,
      L = p U q -> match T, PS with
                   | [], _ => False
                   | [x], [P'] =>
                     exists t, Q = EndOfTrace t q -> Verify [x] p P'
                   | x :: xs, [] => Verify (x :: xs) q Q
                   | x :: xs, P' :: PS' =>
                     Verify (x :: xs) p P' /\ Verify xs (p U q) (UntilPrf PS' P')
                   end

  | AlwaysPrf PS     => forall p,
      L = □ p   -> match T, PS with
                   | [], _ => False
                   | _, [] => False
                   | [x], [P'] => Verify [x] p P'
                   | x :: xs, P' :: PS' =>
                     Verify (x :: xs) p P' /\ Verify xs (□ p) (AlwaysPrf PS')
                   end
  end.
Next Obligation.
  pose proof (Witness_not_empty Q).
  simpl; omega.
Defined.
Next Obligation.
  pose proof (Witness_not_empty P').
  simpl; omega.
Defined.

Notation "T ⊢ L ⟿ P" := (Verify T L P) (at level 80).

Notation "T ⊢[ t ] L ⟿ P" := (@Verify t T L P) (at level 80).

(* Weak Interpretation, where an EndOfTrace is considered a match. *)
Notation "T ⊢~ L ⟿ P" := (@Verify True T L P) (at level 80).

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition ltl_equiv (p q : LTL) : Prop :=
  forall t s P, @Verify t s p P <-> @Verify t s q P.

Local Obligation Tactic := program_simpl.

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
  forall s P, @Verify False s p P <-> @Verify False s q P.

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

Lemma eventually_inv {t s ψ P} :
  s ⊢ ◇ ψ ⟿ P -> s ⊢ ψ ⟿ P \/ tl s ⊢[t] ◇ ψ ⟿ P.
Proof.
  intros.
  induction P.
  - now right.
  - now right.
  - now right.
Admitted.

(* eventually ψ becomes true *)
Lemma eventually_until (ψ : LTL) : ◇ ψ ≈ ⊤ U ψ.
Proof.
  repeat intro; split; intros.
  - induction s; simpl.
      inversion P.
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
