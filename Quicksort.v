Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Definition gtb x y :=match nat_compare x y with Gt => true | _ => false end.

(** Method 1. *)

Program Fixpoint quicksort (l:list nat) {measure (length l)}
  : {sl : list nat | Permutation l sl /\ StronglySorted le sl} :=
  match l with
  | nil => nil
  | x :: xs =>
    match partition (gtb x) xs with
    | (lhs, rhs) => (quicksort lhs) ++ x :: (quicksort rhs)
    end
  end.
Obligation 1. intuition. constructor. Qed.
Obligation 2. admit. Qed.
Obligation 3. admit. Qed.
Obligation 4. admit. Qed.
Obligation 5. admit. Defined.

(** Method 2. *)

Fixpoint partition_spec {A} (xs : list A) : forall P lhs rhs,
  (lhs, rhs) = partition P xs
    -> length lhs <= length xs /\ length rhs <= length xs.
Proof.
  intros.
  induction xs eqn:Heqe; simpl in *.
    inversion H; subst. auto.
  destruct (P a); inversion H; subst; simpl in *.
  intuition.
Admitted.

Program Fixpoint quicksort' (l : list nat) {measure (length l)} : list nat :=
  match l with
  | nil => nil
  | x :: xs =>
    match partition (gtb x) xs with
    | (lhs, rhs) => (quicksort' lhs) ++ x :: (quicksort' rhs)
    end
  end.
Obligation 1.
  pose (partition_spec xs (gtb x) lhs rhs Heq_anonymous).
  simpl. unfold lt. intuition.
Qed.
Obligation 2.
  pose (partition_spec xs (gtb x) lhs rhs Heq_anonymous).
  simpl. unfold lt. intuition.
Qed.
Obligation 3. admit.
Defined.

Lemma quicksort_spec (sl : list nat) : forall l,
  quicksort' l = sl -> Permutation l sl /\ StronglySorted le sl.
Proof.
  intros.
  split; induction l eqn:Heqe.
  - destruct sl. constructor.
    inversion H.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.
