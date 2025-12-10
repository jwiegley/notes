Lemma fibonacci__fib_johnw' :
  forall n m,
    m <= n ->
    fibonacci m = fib_johnw m.
Proof.
  induction n; intros.
  - inversion H. auto.
  - inversion H; subst; auto.
    simpl. destruct n; auto.
Qed.

Theorem fibonacci__fib_johnw :
  forall n,
    fibonacci n = fib_johnw n.
Proof.
  intros.
  apply fibonacci__fib_johnw' with (n:=n). auto.
Qed.