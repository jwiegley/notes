Goal forall C (f : (nat -> nat -> nat) -> C),
  f (fun x y : nat => x + (1 + 2) + y) = f (fun x y : nat => (2 + 1) + x + y).
Proof.
  intros.
  zoom (1 + 2).
    extensionality x.
    extensionality y.
    rewrite (Plus.plus_comm x 1).
    reflexivity.
  reflexivity.
Qed.
