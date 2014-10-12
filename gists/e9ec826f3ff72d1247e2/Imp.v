Lemma ceval_split_if : forall st b c1 c2,
   (beval st b = true  /\ (c1 / st || ceval_fun_no_while st c1)) \/
   (beval st b = false /\ (c2 / st || ceval_fun_no_while st c2)) ->
   (IFB b THEN c1 ELSE c2 FI) / st
   || (if beval st b
       then ceval_fun_no_while st c1
       else ceval_fun_no_while st c2).
Proof.
  intros.
  induction b; intros; simpl;
  inversion H; inversion H0; subst.
  apply E_IfTrue; auto.
  apply E_IfTrue; auto; inversion H1.
  apply E_IfFalse; auto; inversion H1.
  apply E_IfFalse; auto.
  inversion H1; apply E_IfTrue; auto; rewrite H4; assumption.
  inversion H1; apply E_IfFalse; auto; rewrite H4; assumption.
  inversion H1; apply E_IfTrue; auto; rewrite H4; assumption.
  inversion H1; apply E_IfFalse; auto; rewrite H4; assumption.
  inversion H1; apply E_IfTrue; auto; rewrite H4; assumption.
  inversion H1; apply E_IfFalse; auto; rewrite H4; assumption.
  inversion H1; apply E_IfTrue; auto; rewrite H4; assumption.
  inversion H1; apply E_IfFalse; auto; rewrite H4; assumption.
Qed.
