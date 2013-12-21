Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* plus_swap': forall n m p : nat, n + (m + p) = m + (n + p) *)
  intros n m p H.
  apply ev_ev__ev.
  rewrite plus_comm.
  rewrite plus_swap.
  rewrite <- plus_assoc.
  rewrite plus_assoc.
  apply ev_sum. apply H. rewrite <- double_plus. apply double_even.  Qed.
