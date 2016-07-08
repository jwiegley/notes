Example Cypi : forall (t : nat), True.
Proof.
  intros.
  apply (fun x : nat => x : id nat) in t.
  cbv zeta in t.
  exact I.
Defined.

Definition Cypi' := Eval compute [Cypi] in Cypi.