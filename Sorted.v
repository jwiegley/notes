Require Import Coq.Arith.Lt.
Require Import Coq.Bool.Bool.

Open Scope nat_scope.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Fixpoint is_sorted {a : Set} (lt : a -> a -> bool) (xs : list a) : Prop :=
  match xs with
    | nil => True
    | cons x xs => match xs with
      | nil => True
      | cons y ys => if lt x y then is_sorted lt xs else False
      end
  end.

Definition return_sorted_list (xs : list nat)
  : { ys : list nat | is_sorted blt_nat ys }.

Inductive SortedList (a : Set) (lt : a -> a -> bool) : Set :=
  | sl_nil       : SortedList a lt
  | sl_singleton : a -> SortedList a lt
  | sl_cons      : forall (x y : a), Is_true (lt x y) -> SortedList a lt.

Definition return_sorted_list' (xs : list nat) : SortedList nat blt_nat.
