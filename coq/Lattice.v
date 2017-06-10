Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.

Generalizable All Variables.

Reserved Infix "⊓" (at level 40, left associativity).
Reserved Infix "⊔" (at level 36, left associativity).

Class Lattice (A : Type) := {
  meet : A -> A -> A where "x ⊓ y" := (meet x y);
  join : A -> A -> A where "x ⊔ y" := (join x y);

  meet_commutative : forall a b, a ⊓ b = b ⊓ a;
  meet_associative : forall a b c, (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c);
  meet_absorptive  : forall a b, a ⊓ (a ⊔ b) = a;
  meet_idempotent  : forall a,  a ⊓ a = a;

  join_commutative : forall a b, a ⊔ b = b ⊔ a;
  join_associative : forall a b c, (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c);
  join_absorptive  : forall a b, a ⊔ (a ⊓ b) = a;
  join_idempotent  : forall a, a ⊔ a = a
}.

Infix "⊓" := meet (at level 40, left associativity).
Infix "⊔" := join (at level 36, left associativity).

Class Order (A : Type) := {
  ord : relation A;

  reflexive :> Reflexive ord;
  antisymmetric : forall {x y}, ord x y -> ord y x -> x = y;
  transitive :> Transitive ord
}.

Infix "≤" := ord (at level 50).

Class LOSet (A : Set) := {
  order :> Order A;
  lattice :> Lattice A;
  consistent: forall a b, a ≤ b <-> a = a ⊓ b
}.

Section Lattice.

Context `{l : LOSet A}.

Theorem meet_is_glb : forall a b : A,
  forall x, x ≤ a /\ x ≤ b <-> x ≤ a ⊓ b.
Proof.
  split; intros.
    intuition.
    apply consistent in H0.
    apply consistent in H1.
    apply consistent.
    rewrite <- meet_associative, <- H0.
    assumption.
Admitted.

Theorem join_is_lub : forall a b : A,
  forall x, a ≤ x /\ b ≤ x <-> a ⊔ b ≤ x.
Proof.
Admitted.

Inductive Term (A : Type) : Set :=
  | Var  : nat  -> Term
  | Meet : Term -> Term -> Term
  | Join : Term -> Term -> Term.

Fixpoint length (t : Term) : nat :=
  match t with
  | Var n => 1
  | Meet t1 t2 => 1 + length t1 + length t2
  | Join t1 t2 => 1 + length t1 + length t2
  end.

Fixpoint depth (t : Term) : nat :=
  match t with
  | Var n => 0
  | Meet t1 t2 => 1 + max (depth t1) (depth t2)
  | Join t1 t2 => 1 + max (depth t1) (depth t2)
  end.

Inductive Subterm : Term -> Term -> Prop :=
  | Meet1 : forall t1 t2, Subterm t1 (Meet t1 t2)
  | Meet2 : forall t1 t2, Subterm t2 (Meet t1 t2)
  | Join1 : forall t1 t2, Subterm t1 (Join t1 t2)
  | Join2 : forall t1 t2, Subterm t2 (Join t1 t2).

Reserved Notation "〚 t 〛 env" (at level 9).

Fixpoint eval (t : Term) (env : nat -> A) : A :=
  match t with
  | Var n => env n
  | Meet t1 t2 =>〚t1〛env ⊓〚t2〛env
  | Join t1 t2 =>〚t1〛env ⊔〚t2〛env
  end where "〚 t 〛 env" := (eval t env).

Fixpoint interp (t : Term) : A :=
  match t with
  | Var v => v
  | Meet t1 t2 => interp t1 ⊓ interp t2
  | Join t1 t2 => interp t1 ⊔ interp t2
  end.

Definition Leq   (s t : Term) : Prop := forall env, 〚s〛env ≤ 〚t〛env.
Definition Equiv (s t : Term) : Prop := forall env, 〚s〛env = 〚t〛env.

Reserved Infix "≲" (at level 30).

Definition R := symprod Term Term Subterm Subterm.

Open Scope lazy_bool_scope.

Program Fixpoint leq (p : Term * Term) {wf R p} :
  { b : bool | Is_true b -> Leq (fst p) (snd p) } :=
  match p with
  | (s, t) =>
    let leqb x y := proj1_sig (leq (x, y)) in
    match (s, t) with
    | (Var i, Var j)           => nat_eq_bool i j
    | (Join s1 s2, t)          => leqb s1 t &&& leqb s2 t
    | (s, Meet t1 t2)          => leqb s t1 &&& leqb s t2
    | (Var m, Join t1 t2)      => leqb s t1 ||| leqb s t2
    | (Meet s1 s2, Var n)      => leqb s1 t ||| leqb s2 t
    | (Meet s1 s2, Join t1 t2) => leqb s1 t ||| leqb s2 t ||| leqb s t1 ||| leqb s t2
    end
  end where "s ≲ t" := (leq (s, t)).
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Import ListNotations.

Ltac intern vars e :=
  let rec loop n vars' :=
    match vars' with
    | [] =>
      let vars'' := eval simpl in (vars ++ [e]) in
      constr:((n, vars''))
    | e :: ?vars'' => constr:((n, vars))
    | _ :: ?vars'' => loop (S n) vars''
    end in
  loop 0 vars.

Ltac reflect env m j t :=
  match t with
  | (m ?X1 ?X2) =>
    let r1 := reflect env m j X1
      with r2 := reflect env m j X2 in
    constr:(Meet r1 r2)
  | (j ?X1 ?X2) =>
    let r1 := reflect env m j X1
      with r2 := reflect env m j X2 in
    constr:(Join r1 r2)
  (* | ?X1 => *)
  (*   let n := inv_lookup env X1 in *)
  (*   constr:(Var n) *)
  end.

Lemma leq_correct : forall t u : Term,
  Is_true (` (leq (t, u))) -> forall env,〚t〛env ≤〚u〛env.
Proof.
Admitted.

Lemma median_inequality : forall x y z : A,
  (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x).
Proof.
  intros.
  destruct l.
  reflect (fun n : nat => A) meet join ((x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ x ⊔ y ⊓ y ⊔ z ⊓ z ⊔ x).
  evar (env : nat -> A).
  change ((x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ x ⊔ y ⊓ y ⊔ z ⊓ z ⊔ x)
    with (〚(x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x)〛env ≤〚x ⊔ y ⊓ y ⊔ z ⊓ z ⊔ x〛env).
Admitted.

End Lattice.
