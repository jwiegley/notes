Require Import List.

Set Implicit Arguments.

CoInductive stream : Set :=
  | Cons : nat -> stream -> stream.

CoFixpoint fib' (n m : nat) := Cons n (fib' m (n+m)).

Fixpoint approx (s : stream) (n : nat) : list nat.
Proof.
  destruct n.
    exact nil.
  destruct s as [h t].
  simpl in n.
  pose proof (approx t n).
  simpl in H.
  exact (h :: H).
Defined.

Eval hnf in (approx (fib' 1 1) 40).
Eval hnf in (approx (fib' 1 (1 + 1)) 39).
Eval hnf in (approx (fib' (1 + 1) (1 + (1 + 1))) 38).
Eval hnf in (approx (fib' (1 + (1 + 1)) (1 + 1 + (1 + (1 + 1)))) 37).
