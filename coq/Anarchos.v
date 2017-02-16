Require Import Coq.Arith.Peano_dec.

Definition T := {n | n < 256}.

Theorem T_eq_dec : forall (t1 t2 : T), {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1.
  intro t2.
  destruct t2.
  destruct (Peano_dec.eq_nat_dec x x0).
    left.
    f_equal.
    revert l l0.
    rewrite e; clear e x.
    intros l l0.
    f_equal.
    apply Peano_dec.le_unique.
  right.
  intro H.
  inversion H.
  contradiction.
Qed.

Require Coq.Program.Equality.

Import EqNotations.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Definition ev_sum (n m : nat) (H1 : ev n) (H2 : ev m) : ev (n + m) :=
  let fix proof (n : nat) (H1 : ev n) : ev (n + m) :=
      match H1 with
      | ev_0       => rew <- plus_O_n m in H2
      | ev_SS n' H => ev_SS (n' + m) (proof n' H)
      end in
  proof n H1.

Definition ev_sum' (n m : nat) (H1 : ev n) (H2 : ev m) : ev (n + m) :=
  let fix proof (n : nat) (H1 : ev n) (m : nat) (H2 : ev m) : ev (n + m) :=
      match H1 with
      | ev_0       => rew <- plus_O_n m in H2
      | ev_SS n' H => ev_SS (n' + m) (proof n' H m H2)
      end in
  proof n H1 m H2.

Proof.
Program Definition foo :=
  let y := 10 in
  let fix proof (n : nat) (H : n < y) : { n' : nat | n <= n' <= y } :=
      match n with
      | O => 0
      | S x =>
        proof x _
      end in
  proof 5.
Obligation 1. omega. Qed.
Obligation 2. omega. Qed.
Obligation 3. admit. Qed.

(* Now generalizing y: *)

Program Definition bar :=
  let fix IHn (n y : nat) (H : n < y) : { n' : nat | n <= n' <= y } :=
      exist _ n _ in
  IHn 5.

Theorem foo (x y : nat) : x < y -> = y + x.
Proof.
  induction x.
    induction y.
      auto.
    omega.
  omega.

Definition Anarchos := { n : nat | n < 256 }.

Lemma Anarchos_dec (x y : Anarchos) : {x = y} + {x <> y}.
Proof.
  destruct x; destruct y.

Inductive BigType :=
  | A
  | B
  | C.

Inductive true_xor_false (x : BigType) (f : BigType -> bool) :
  bool -> bool -> Set :=
  | EqNotNeq : f x = true -> true_xor_false x f true false
  | NeqNotEq : negb (f x) = true -> true_xor_false x f false true.

Lemma matchP (x : BigType) (f : BigType -> bool) :
  true_xor_false x f (f x) (negb (f x)).
Proof.
  destruct (f x) eqn:E.
    constructor.
    assumption.
  constructor.
  rewrite E.
  reflexivity.
Qed.

Definition is_B (x : BigType) : bool :=
  match x with
    | A => false
    | B => true
    | C => false
  end.

Lemma check_B (x : BigType) : is_B x = true.
Proof.
  destruct (matchP x is_B) as [Htrue|Hfalse].
    reflexivity.
  (* of course we can't prove that every x is a B! *)
  admit.
Qed.
