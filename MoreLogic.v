Lemma negb_flip : forall {X} (x : X) (test : X -> bool),
  negb (test x) = true -> test x = false.
Proof.
  intros. destruct (test x). inversion H. reflexivity.
Qed.

(* Given statements of truth in the context, and a goal which can be
   determined solely from those statements, discharge the goal. *)
Ltac elim_truth :=
  repeat (match goal with
  | [ H: andb (negb ?X) _ = true |- (if ?X then _ else _) = _ ] =>
    assert (X = false) as Hfalse by solve [
      apply andb_true_elim1 in H;
      apply negb_flip in H;
      assumption
    ]; rewrite Hfalse; clear Hfalse
  | [ H: andb ?X _ = true |- (if ?X then _ else _) = _ ] =>
    assert (X = true) as Htrue by solve [
      apply andb_true_elim1 in H;
      assumption
    ]; rewrite Htrue; clear Htrue
  | [ H: andb _ ?X = true |- ?X = true ] =>
      apply andb_true_elim2 in H;
      assumption
  end); auto.

Theorem filter_challenge : forall {X} (test : X -> bool) (l l1 l2 : list X),
  let T := fun x => test x = true  in
  let F := fun x => test x = false in
  in_order_merge l1 l2 l
    -> forallb test l1 = true
    -> forallb (fun x => negb (test x)) l2 = true -> filter test l = l1.
Proof.
  Ltac logic_puzzle hyp :=
    simpl in *; elim_truth;
    try (try f_equal; apply hyp; elim_truth).

  intros. induction H; subst; simpl.
  - induction l. auto. logic_puzzle IHl.
  - induction l. auto. logic_puzzle IHl.
  - logic_puzzle IHin_order_merge.
  - logic_puzzle IHin_order_merge.
Qed.
