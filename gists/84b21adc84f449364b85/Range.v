Functional Scheme even_ind := Induction for even Sort Prop.

Lemma ltn_even : forall n m, even n && even m -> n < m -> n.+1 < m.
Proof.
  move=> n m; move: n.
  functional induction even m.
  - by done.
  - by move=> ? /andP [_ Hcontra] //.
  - move=> n Hev Hlt.
    apply/ltnW/ltnW.
    rewrite -addn2 -[n'.+2]addn2 leq_add2r.
    apply IHb. apply Hev.

(* 1 subgoals, subgoal 1 (ID 4999) *)

(*   n' : nat *)
(*   IHb : ∀ n : nat, even n && even n' → n < n' → n.+1 < n' *)
(*   n : nat *)
(*   Hev : even n && even n' *)
(*   Hlt : n < n'.+2 *)
(*   ============================ *)
(*    n < n' *)
Admitted.
