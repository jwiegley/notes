Require Import List.
Require Import Arith.

Fixpoint append {X} xs ys : list X :=
  match xs with
  | nil => ys
  | x :: xs' => x :: (append xs' ys)
  end.

Theorem concat_sum :
  forall X : Type,
  forall xs : list X,
  forall ys : list X,
  length (append xs ys) = (length xs) + (length ys).
Proof.
  intros X xs ys. induction xs as [| x].
  - reflexivity.
  - simpl. rewrite -> IHxs. reflexivity.
Qed.
