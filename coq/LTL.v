Require Import Program.
Require Import FunctionalExtensionality.

Open Scope program_scope.

Generalizable All Variables.

Class Monoid (a : Type) := {
  mempty : a;
  mappend : a -> a -> a;

  mempty_left : forall x, mappend mempty x = x;
  mempty_right : forall x, mappend x mempty = x;
  mappend_assoc : forall x y z,
    mappend x (mappend y z) = mappend (mappend x y) z
}.

Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None;
  mappend := fun x y =>
    match x, y with
    | None, x => x
    | x, None => x
    | Some x, Some y => Some (mappend x y)
    end
}.
Next Obligation. destruct x; auto. Qed.
Next Obligation.
  destruct x, y, z; auto.
  now rewrite mappend_assoc.
Qed.

Class Functor (f : Type -> Type) := {
  fmap {a b} : (a -> b) -> f a -> f b;

  fmap_id : forall x, fmap id = @id (f x);
  fmap_comp : forall x y z (f : y -> z) (g : x -> y),
    fmap (f ∘ g) = fmap f ∘ fmap g
}.

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure {a} : a -> f a;
  liftA2 {a b c} : (a -> b -> c) -> f a -> f b -> f c
}.

Program Instance Functor_arrow {x} : Functor (fun y => x -> y) := {
  fmap := fun _ _ => compose
}.

Program Instance Applicative_arrow {x} : Applicative (fun y => x -> y) := {
  pure := fun _ x _ => x;
  liftA2 := fun _ _ _ f x y v => f (x v) (y v);
}.

Program Instance Functor_option : Functor option := {
  fmap := fun _ _ f x =>
    match x with
    | None => None
    | Some x => Some (f x)
    end
}.
Next Obligation.
  extensionality y.
  destruct y; auto.
Qed.
Next Obligation.
  extensionality w.
  destruct w; auto.
Qed.

Program Instance Applicative_option : Applicative option := {
  pure := fun _ x => Some x;
  liftA2 := fun _ _ _ f x y =>
    match x, y with
    | None, _ => None
    | _, None => None
    | Some x, Some y => Some (f x y)
    end
}.

Definition Proof (b : Type) := option b.

Definition Proposition (a b : Type) := a -> Proof b.

Definition Stream (a : Type) := nat -> a.

Program Instance Functor_Stream : Functor Stream := Functor_arrow.
Program Instance Applicative_Stream : Applicative Stream := Applicative_arrow.

(* An LTL formula on a stream of elements of type 'a' returns Nothing if the
   formula does not hold from the start of the stream, or else it advances
   the stream for the elements the formula pertained to, plus a monoid
   accumulation of the proof witnesses for the formula. *)
Definition Formula (a b : Type) := Stream a -> Proof b.

Program Instance Functor_Formula {a} : Functor (Formula a) := {
  fmap := fun _ _ f x v => fmap f (x v)
}.
Next Obligation.
  extensionality y.
  extensionality z.
  unfold id.
  destruct (y z); auto.
Qed.
Next Obligation.
  extensionality w.
  extensionality v.
  unfold compose.
  destruct (w v); auto.
Qed.

Program Instance Applicative_Formula {a : Type} : Applicative (Formula a) := {
  pure := fun _ x _ => Some x
}.
Next Obligation.
Admitted.

Section LTL.

Variable a : Set.

Inductive LTL : Set :=
  | Var (x : a)
  | Truth
  | Not (p : LTL)
  | Or (p q : LTL)
  | Next (p : LTL)
  | Until (p q : LTL).

Notation "¬ x" := (Not x) (at level 50).
Infix "∨" := Or (at level 50).
Notation "'X' x" := (Next x) (at level 50).
Notation "p 'U' q" := (Until p q) (at level 50).

Fixpoint eval (p : LTL) (s : Stream a) : Prop :=
  match p with
  (* w ⊨ p if p ∈ w(0) *)
  | Var x => s 0 = x

  | Truth => True

  (* w ⊨ ¬ψ if w ⊭ ψ *)
  | Not p => ~ (eval p s)

  (* w ⊨ φ ∨ ψ if w ⊨ φ or w ⊨ ψ *)
  | Or p q => eval p s \/ eval q s

  (* w ⊨ X ψ if w1 ⊨ ψ (in the next time step ψ must be true) *)
  | Next p => eval p (s ∘ S)

  (* w ⊨ φ U ψ if there exists i ≥ 0 such that wi ⊨ ψ and for all 0 ≤ k < i, wk ⊨ φ
     (φ must remain true until ψ becomes true) *)
  | Until p q => exists i : nat,
      eval q (s ∘ plus i) /\ forall k, 0 <= k < i -> eval p (s ∘ plus k)
  end.

Definition and (φ ψ : LTL) := ¬(¬φ ∨ ¬ψ).
Infix "∧" := and (at level 50).

Definition impl (φ ψ : LTL) := ¬φ ∨ ψ.
Infix "→" := impl (at level 50).

Definition iff (φ ψ : LTL) := (φ → ψ) ∧ (ψ → φ).
Infix "↔" := iff (at level 50).

Definition true : LTL := Truth.
Definition false : LTL := ¬true.

(* φ R ψ = ¬(¬φ U ¬ψ)
  (ψ remains true until and including once φ becomes true.
   If φ never become true, ψ must remain true forever.) *)
(* F ψ = true U ψ (eventually ψ becomes true) *)
(* G ψ = false R ψ = ¬F ¬ψ (ψ always remains true) *)

(* φ W ψ = (φ U ψ) ∨ G φ = φ U (ψ ∨ G φ) = ψ R (ψ ∨ φ) *)
(* φ U ψ = Fψ ∧ (φ W ψ) *)
(* φ R ψ = ψ W (ψ ∧ φ) *)
(* φ M ψ = ¬(¬φ W ¬ψ) = (φ R ψ) ∧ F φ = φ R (ψ ∧ F φ) = ψ U (φ ∧ ψ) *)

(** Distributivity *)

(* X (φ ∨ ψ) = (X φ) ∨ (X ψ) *)
(* X (φ ∧ ψ)= (X φ) ∧ (X ψ) *)
(* X (φ U ψ)= (X φ) U (X ψ) *)
(* F (φ ∨ ψ) = (F φ) ∨ (F ψ) *)
(* G (φ ∧ ψ)= (G φ) ∧ (G ψ) *)
(* ρ U (φ ∨ ψ) = (ρ U φ) ∨ (ρ U ψ) *)
(* (φ ∧ ψ) U ρ = (φ U ρ) ∧ (ψ U ρ) *)

(** Negation propagation *)

(* X is self-dual *)
(* F and G are dual *)
(* U and R are dual *)
(* W and M are dual *)
(* ¬X φ = X ¬φ *)
(* ¬F φ = G ¬φ *)
(* ¬ (φ U ψ) = (¬φ R ¬ψ) *)
(* ¬ (φ W ψ) = (¬φ M ¬ψ) *)
(* ¬G φ = F ¬φ *)
(* ¬ (φ R ψ) = (¬φ U ¬ψ) *)
(* ¬ (φ M ψ) = (¬φ W ¬ψ) *)

(** Special Temporal properties *)

(*   F φ = F F φ *)
(*   G φ = G G φ *)
(* φ U ψ = φ U (φ U ψ) *)
(* φ U ψ = ψ ∨ (φ ∧ X(φ U ψ)) *)
(* φ W ψ = ψ ∨ (φ ∧ X(φ W ψ)) *)
(* φ R ψ = ψ ∧ (φ ∨ X(φ R ψ)) *)
(*   G φ = φ ∧ X(G φ) *)
(*   F φ = φ ∨ X(F φ) *)

End LTL.
