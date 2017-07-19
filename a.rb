Require Import Coq.Arith.Arith.

Open Scope nat_scope.

Goal forall (n m : nat) (H : n < n + S m) (P : n < n + S m -> Prop), P H.
Proof.
  intros.
  Fail rewrite Nat.add_succ_r in H, P.
Abort.
