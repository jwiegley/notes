Require Import Coq.Arith.Plus.

Lemma kba : forall p' q fib,
    fib (S p') * fib (S q) + fib p' * fib (S q) +
    fib (S p') * fib q + fib (S p') * fib (S q) + fib p' * fib q =
    fib (S p') * fib (S q) + fib p' * fib (S q) +
    fib (S p') * fib (S q) + fib (S p') * fib q + fib p' * fib q.
Proof.
  intros.
  remember (fib (S p') * fib (S q)) as n'.
  remember (fib p' * fib q) as n.
  remember (fib p' * fib (S q)) as m.
  remember (fib (S p') * fib q) as m'.
  repeat rewrite <- plus_assoc.
  rewrite (plus_permute m').
  reflexivity.
Qed.
