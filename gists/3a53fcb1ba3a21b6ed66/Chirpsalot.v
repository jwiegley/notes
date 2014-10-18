Fixpoint fibonacci__fib_johnw n :
  fibonacci n = fib_johnw n.
Proof.
  induction n as [| n'].
    reflexivity.
  simpl. destruct n'. reflexivity.
  simpl pred. rewrite IHn'. f_equal.
  apply fibonacci__fib_johnw.
Qed.
