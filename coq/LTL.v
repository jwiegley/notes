Require Import Program.
(* Require Import FunctionalExtensionality. *)
Require Import Coq.Lists.List.
Require Import Coq.Classes.Equivalence.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Open Scope program_scope.
Open Scope list_scope.

Generalizable All Variables.
Set Transparent Obligations.
Set Decidable Equality Schemes.

Section LTL.

Variable a : Type.              (* The type of entries in the trace *)
Variable b : Type.              (* The type of data derived from each entry *)

Definition Stream := list a.

Inductive LTL : Type :=
  (* Boolean layer *)
  | Top
  | Bottom
  | Query (v : a -> option b)
  | And (p q : LTL)
  | Or (p q : LTL)
  | Impl (p q : LTL)

  (* Temporal layer *)
  | Next (p : LTL)
  | Eventually (p : LTL)
  | Until (p q : LTL)
  | Always (p : LTL).

Notation "⊤"       := Top             (at level 50).
Notation "⊥"       := Bottom          (at level 50).
Notation "¬ x"     := (Impl x Bottom) (at level 50).
Infix    "∧"       := And             (at level 50).
Infix    "∨"       := Or              (at level 50).
Infix    "→"       := Impl            (at level 50).
Notation "'X' x"   := (Next x)        (at level 50).
Notation "◇ x"     := (Eventually x)  (at level 50).
Notation "p 'U' q" := (Until p q)     (at level 50).
Notation "□ x"     := (Always x)      (at level 50).

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

Definition remaining (p : LTL) (s : Stream) := LTL_size p + length s.

Local Obligation Tactic := program_simpl; unfold remaining; simpl; try omega.

(* [term] is a type that is found at the end of a partial trace match. By
   choosing [False], one can express that formula must exactly match within a
   trace. *)
Variable term : Prop.

Equations matches (l : LTL) (s : Stream) : Prop by wf (remaining l s) lt :=
  (*  1 *) matches (⊤)       _         := True;
  (*  2 *) matches (⊥)       _         := False;
  (*  3 *) matches (Query v) []        := term;
  (*  4 *) matches (Query v) (x :: _)  := exists b, v x = Some b;
  (*  5 *) matches (p ∧ q)   s         := matches p s /\ matches q s;
  (*  6 *) matches (p ∨ q)   s         := matches p s \/ matches q s;
  (*  7 *) matches (p → q)   s         := matches p s -> matches q s;
  (*  8 *) matches (X p)     (_ :: xs) := matches p xs;
  (*  9 *) matches (X p)     []        := term;
  (* 10 *) matches (◇ p)     (x :: xs) := matches p (x :: xs) \/ matches (◇ p) xs;
  (* 11 *) matches (◇ p)     []        := term;
  (* 12 *) matches (p U q)   [x]       := matches q [x] \/ matches p [x];
  (* 13 *) matches (p U q)   (x :: xs) := matches q (x :: xs) \/
                                          (matches p (x :: xs) /\ matches (p U q) xs);
  (* 14 *) matches (p U q)   []        := term;
  (* 15 *) matches (□ p)     (x :: xs) := matches p (x :: xs) /\ matches (□ p) xs;
  (* 16 *) matches (□ p)     []        := True.

Inductive Match : Type :=
  | EndOfTrace (t : term)
  | IsTrue
  | Base (x : b)
  | Both (p q : Match)
  | InLeft (p : Match)
  | InRight (q : Match)
  | NotImplied
  | Implied (p q : Match)
  | NextFwd (p : Match)
  | EventuallyStop (p : Match)
  | EventuallyFwd (p : Match)
  | UntilPrf1 (q : Match)
  | UntilPrf2 (p : Match)
  | UntilPrf3 (p : Match) (ps : Match)
  | AlwaysPrf1 (p : Match) (ps : Match)
  | AlwaysPrf2.

Equations compare (t : option term) (L : LTL) (T : Stream) : option Match
  by wf (remaining L T) lt :=

  compare t (⊤) _ := Some IsTrue;
  compare t (⊥) _ := None;

  compare t (Query v) (x :: _) :=
    match v x with
    | None => None
    | Some r => Some (Base r)
    end;

  compare t (Query v) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (And p q) T :=
    match compare t p T with
    | None   => None
    | Some P =>
      match compare t q T with
      | None   => None
      | Some Q => Some (Both P Q)
      end
    end;

  compare t (Or p q) T :=
    match compare t p T with
    | None   =>
      match compare t q T with
      | None   => None
      | Some Q => Some (InRight Q)
      end
    | Some P => Some (InLeft P)
    end;

  compare t (Impl p q) T :=
    match compare t p T with
    | None   => Some NotImplied
    | Some P =>
      match compare t q T with
      | None   => None
      | Some Q => Some (Implied P Q)
      end
    end;

  compare t (Next p) (_ :: xs) :=
    match compare t p xs with
    | None => None
    | Some P => Some (NextFwd P)
    end;

  compare t (Next p) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Eventually p) (x :: xs) :=
    match compare t p (x :: xs) with
    | None =>
      match compare t p xs with
      | None => None
      | Some P => Some (EventuallyFwd P)
      end
    | Some P => Some (EventuallyStop P)
    end;

  compare t (Eventually p) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Until p q) (x :: xs) :=
    match compare t q (x :: xs) with
    | Some Q => Some (UntilPrf1 Q)
    | None =>
      match xs with
      | [] =>
        match compare t p [x] with
        | Some P => Some (UntilPrf2 P)
        | None => None
        end
      | _ =>
        match compare t p (x :: xs) with
        | None => None
        | Some P =>
          match compare t (p U q) xs with
          | Some Q => Some (UntilPrf3 P Q)
          | None => None
          end
        end
      end
    end;

  compare t (Until p q) [] :=
    match t with
    | None => None
    | Some t => Some (EndOfTrace t)
    end;

  compare t (Always p) (x :: xs) :=
    match compare t p (x :: xs) with
    | None => None
    | Some P =>
      match compare t (Always p) xs with
      | None => None
      | Some PS => Some (AlwaysPrf1 P PS)
      end
    end;

  compare t (Always p) [] := Some AlwaysPrf2.

Ltac simplify_compare_in H :=
  repeat rewrite
    ?compare_equation_1,
    ?compare_equation_2,
    ?compare_equation_3,
    ?compare_equation_4,
    ?compare_equation_5,
    ?compare_equation_6,
    ?compare_equation_7,
    ?compare_equation_8,
    ?compare_equation_9,
    ?compare_equation_10,
    ?compare_equation_11,
    ?compare_equation_12,
    ?compare_equation_13,
    ?compare_equation_14,
    ?compare_equation_15
    in H.

Ltac simplify_matches_in H :=
  repeat rewrite
    ?matches_equation_1,
    ?matches_equation_2,
    ?matches_equation_3,
    ?matches_equation_4,
    ?matches_equation_5,
    ?matches_equation_6,
    ?matches_equation_7,
    ?matches_equation_8,
    ?matches_equation_9,
    ?matches_equation_10,
    ?matches_equation_11,
    ?matches_equation_12,
    ?matches_equation_13,
    ?matches_equation_14,
    ?matches_equation_15
    in H.

Lemma Compute_Verified (t : option term) (L : LTL) (T : Stream) :
  forall P, compare t L T = Some P -> matches L T.
Proof.
  induction L, T; simpl; intros; try constructor;
  simplify_compare_in H;
  repeat rewrite
    ?matches_equation_1,
    ?matches_equation_2,
    ?matches_equation_3,
    ?matches_equation_4,
    ?matches_equation_5,
    ?matches_equation_6,
    ?matches_equation_7,
    ?matches_equation_8,
    ?matches_equation_9,
    ?matches_equation_10,
    ?matches_equation_11,
    ?matches_equation_12,
    ?matches_equation_13,
    ?matches_equation_14,
    ?matches_equation_15;
  try discriminate;
  simpl in *; auto.
  - destruct t; [|discriminate].
    assumption.
  - destruct (v a0) eqn:?; [|discriminate].
    now exists b0.
  - destruct (compare t L1 []) eqn:?; [|discriminate].
    destruct (compare t L2 []) eqn:?; [|discriminate].
    inversion H; subst; clear H.
    specialize (IHL1 m eq_refl).
    specialize (IHL2 m0 eq_refl).
    admit.
  - admit.
Abort.

Notation "T ⊢ L ⟿ P" := (compare T L = Some P) (at level 80).

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

(* (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
Definition release (φ ψ : LTL) := ¬(¬φ U ¬ψ).
Notation "p 'R' q" := (release p q) (at level 50).

Definition ltl_equiv (p q : LTL) : Prop.
Admitted.

(*
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
  specialize (H s).
  specialize (H0 s).
  now rewrite H, H0.
Qed.
*)

Infix "≈" := equiv (at level 90).

Ltac end_of_trace := apply EndOfTrace; [auto|intro; discriminate].

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

Lemma witness_neg s φ : s ⊢ ¬φ <-> ~ (s ⊢ φ).
Proof.
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
