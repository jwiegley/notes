Require Import List.
Import ListNotations.

Fixpoint fibonacci (n:nat) : nat :=
  match n with
    | 0 => 1
    | S 0 => 1
    | S x => fibonacci x + fibonacci (pred x)
  end.

Fixpoint fib_johnw (n:nat) : nat :=
  match n with
    | 0 => 1
    | S x => match x with 0 => 1 | S x' => fib_johnw x + fib_johnw x' end
  end.

Fixpoint downFrom (n:nat) : list nat :=
  match n with
    | 0 => [0]
    | S x => S x :: downFrom x
  end.

Definition upTo (n:nat) := rev (downFrom n).

Example fib_meh :
  map fibonacci (upTo 20) = [1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610; 987; 1597; 2584; 4181; 6765; 10946].
Proof.
  reflexivity.
Qed.

Example fib_meh' :
  map fib_johnw (upTo 20) = [1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610; 987; 1597; 2584; 4181; 6765; 10946].
Proof.
  reflexivity.
Qed.

Fixpoint fibonacci__fib_johnw n :
  fibonacci n = fib_johnw n.
Proof.
  induction n as [| n'].
    reflexivity.
  simpl. destruct n'. reflexivity.
  simpl pred. rewrite IHn'. f_equal.
  apply fibonacci__fib_johnw.
Qed.
