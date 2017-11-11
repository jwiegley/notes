Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Omega.
Ltac solve_quicksort_termination :=
  Coq.Program.Tactics.program_simpl;
  match goal with [ H : (_,_) = partition _ _ |- _ ] =>
    symmetry in H end;
  match goal with [ H : partition _ _ = (_,_) |- _ ] =>
    apply partition_length in H end;
  simpl;Omega.omega.

Require Coq.Program.Wf.
Program Fixpoint quicksort (xs : list nat) { measure (length xs) } : list nat :=
match xs with
  | [] => []
  | p :: ys => match partition (fun x => Nat.ltb x p) ys with
     | (lesser, greater) =>
        quicksort lesser ++ [p] ++ quicksort greater
     end
end.
Solve Obligations with (solve_quicksort_termination).

Require Import Coq.Sorting.Permutation.
Theorem quicksort_permutation:
  forall xs, Permutation(quicksort xs) xs.
Proof.
  intros.
  remember (length xs) as n.
  generalize dependent xs.
  induction n using lt_wf_ind.
  intros.
  destruct xs.
  * apply perm_nil.
  * simpl.
    (* Goal now: Permutation (quicksort (n0 :: xs)) (n0 :: xs) *)
    (* How do I reduce that to the RHS of quicksort? *)
Abort.

Axiom funext : forall {A B} {f g : A -> B}, (forall x, f x = g x) -> f = g.
Theorem quicksort_equation (xs : list nat) :
  quicksort xs = match xs with
                 | [] => []
                 | p :: ys => match partition (fun x => Nat.ltb x p) ys with
                              | (lesser, greater) =>
                                quicksort lesser ++ [p] ++ quicksort greater
                              end
                 end.
Proof.
  unfold quicksort; rewrite Wf.Fix_eq; fold quicksort.
  - unfold proj1_sig.
    destruct xs as [|x xs]; auto.
    destruct (partition _ xs) as [lesser greater] eqn:split_partition.
    reflexivity.
  - intros xs' f g eq_fg.
    destruct xs' as [|x' xs']; auto.
    simpl.
    rewrite (funext eq_fg).
    reflexivity.
Qed.