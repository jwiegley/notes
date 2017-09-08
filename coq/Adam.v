Require Import Coq.Program.Tactics.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Fixpoint zip {A} (xs ys : list A) : list (A * A) :=
  match xs, ys with
  | nil, _ => nil
  | _, nil => nil
  | cons x xs, cons y ys => (x, y) :: zip xs ys
  end.

Program Definition prod_nat_eq_dec (x y : nat * nat) : {x = y} + {x <> y} :=
  match Nat.eq_dec (fst x) (fst y) with
  | left _  =>
    match Nat.eq_dec (snd x) (snd y) with
    | left _   => left _
    | right _  => right _
    end
  | right _  => right _
  end.

Definition lists_perm (xs ys : list nat) : bool :=
  if (length xs =? length ys)%nat
  then
    match fold_right (fun '(x, y) k =>
                        fun xs =>
                          match xs with
                          | nil => None
                          | xs  => k (remove prod_nat_eq_dec (y, x) xs)
                          end) (fun _ => None)
                     (zip xs ys) (zip xs ys) with
    | None => false
    | Some zs => match list_eq_dec prod_nat_eq_dec nil zs with
                 | left _ => true
                 | right _ => false
                 end
    end
  else false.

Import ListNotations.

Compute lists_perm [1; 3; 2] [2; 1; 3].