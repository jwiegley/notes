Require Import Coq.Arith.Arith.

Open Scope nat_scope.

Definition talia_the_cookie_bringer (n m : nat) (H : n < n + S m)
           (P : n < n + S m -> Prop) : Prop :=
  (eq_rect (n + S m) (fun x => n < x -> Prop) P (S (n + m)) (Nat.add_succ_r n m))
    (eq_ind (n + S m) (fun x => n < x) H (S (n + m)) (Nat.add_succ_r n m)).
