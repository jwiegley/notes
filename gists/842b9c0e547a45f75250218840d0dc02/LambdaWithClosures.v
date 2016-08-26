Example notReduceInfinite:
  ~ (exists result,
      SymReduce
        (App (Lam 0 (App (Var 0) (Var 0))) (Lam 0 (App (Var 0) (Var 0))))
        result).
Proof.
  Require Import Coq.Logic.Classical_Pred_Type.
  apply all_not_not_ex; unfold not; intros.
  Ltac inv H := inversion H; subst; clear H.
  Ltac reduction :=
    repeat match goal with
           | [ H : SymReduce _ _ |- _ ] => inv H
           | [ H : Subst _ _ _ _ |- _ ] => inv H
           end.
  induction n; reduction; intuition.
  apply IHn1; intuition.
  eapply SRApp; try eapply SRLam.
  (* We are lacking a constructor for [Subst e x y (Lam _ y)] ... *)
Abort. (* Can't figure out how to prove this with big-step reduction. *)
