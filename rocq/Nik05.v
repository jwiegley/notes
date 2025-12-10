Inductive vec (A : Type) : nat -> Type :=
  | E : vec A 0
  | C : forall {n}, A -> vec A n -> vec A (S n)
.

Definition vhead {A : Type} {n : nat} (v : vec A (S n)) : A :=
  match v with
  | C _ a _ => a
  (* Works fine without E clause. *)
  end
.

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.JMeq.

Import EqNotations.

Definition vlast {A : Type} {n : nat} (v : vec A (S n)) : A.
Proof.
  induction n.
    inversion v.
    exact X.
  inversion v.
  exact (IHn X0).
Defined.

Definition vlast' {A} := Eval compute[vlast nat_rect] in @vlast A.
Print vlast'.
Print Assumptions vlast.

Program Fixpoint vlast {A : Type} {n : nat} (v : vec A (S n)) {struct v} : A :=
  match v in vec _ n' return n' = S n -> A with
  | E _ => fun _ => False_rect _ _
  | C _ a (E _) => fun _ => a
  | @C _ 0 a _ => fun _ => a
  | @C _ (S n0) a r => fun (H : S (S n0) = S n) => vlast r
  end eq_refl
.
