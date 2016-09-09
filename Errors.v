Require Import PeanoNat Fiat.ADT.

Definition alloc (r : nat) : Comp (nat * nat) :=
  addr <- { addr : nat | r < 100 };
  ret (r + 1, addr).

Lemma final_refinement :
  { f : nat -> option (nat * nat)%type
  | forall r r', f r = Some r' -> alloc r ↝ r' }.
Proof.
  exists (fun r =>
              if r <? 100
              then Some (r + 1, r)
              else None).
  intros.
  destruct (r <? 100) eqn:Heqe.
    unfold alloc.
    apply BindComputes with (a:=r).
      apply PickComputes.
      apply Nat.ltb_lt; assumption.
    inversion H.
    constructor.
  discriminate.
Qed.