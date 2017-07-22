Require Import List.

Set Implicit Arguments.

CoInductive stream : Set :=
  | Cons : nat -> stream -> stream.

CoFixpoint fib' (n m : nat) := Cons n (fib' m (n+m)).

Fixpoint approx (s : stream) (n : nat) : list nat :=
  match s, n with
  | _, 0 => nil
  | Cons x xs, S n => cons x (approx xs n)
  end.

Eval simpl in (approx (fib' 1 1) 10).
