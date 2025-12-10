Require Import Coq.Lists.List.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.

Set Implicit Arguments.
Set Strict Implicit.

Arguments MZ {_ _ _}.
Arguments MN {_ _ _ _} _.

Section del_val.
  Context {T : Type}.
  Variable ku : T.

  Fixpoint del_member (ls : list T) (m : member ku ls) : list T :=
    match m with
    | @MZ _ _ l => l
    | @MN _ _ ku' _ m => ku' :: del_member m
    end.
End del_val.

Section member_heq.
  Context {T : Type}.

  Program Fixpoint member_heq (l r : T) (ls : list T) (m : member l ls)
  : member r ls -> member r (del_member m) + (l = r) :=
    fun (m' : member r ls) =>
      match m in member _ ls0 return ls = ls0 -> member r (del_member m) + (l = r) with
      | MZ =>
        match m' with
        | MZ => fun _ => inr eq_refl
        | MN _ => fun _ => inl _
        end
      | @MN _ _ ku1 ls1 m1 => fun (H : ls = ku1 :: ls1) =>
        match m' with
        | MZ => inl MZ
        | @MN _ _ ku2 ls2 m2 => member_heq m1 m2
        end
      end eq_refl.
  Print Assumptions member_heq.

(*
  Definition member_heq (l r : T) (ls : list T) (m : member l ls)
  : member r ls -> member r (del_member m) + (l = r).
    induction m; simpl; intros;
    inversion X; subst; clear X.
    - right; reflexivity.
    - left; assumption.
    - left; constructor.
    - destruct (IHm X0).
        left; constructor; assumption.
      right; assumption.
  Defined.
  Print Assumptions member_heq.
*)

  Lemma member_heq_eq
  : forall {l l' ls} (m1 : member l ls) (m2 : member l' ls) pf,
      member_heq m1 m2 = inr pf ->
      match pf in _ = X return member X ls with
      | eq_refl => m1
      end = m2.
  Proof.
    intros.
    destruct pf.
    unfold member_heq in H.
  Admitted.
  Print Assumptions member_heq_eq.

End member_heq.

Arguments member_heq_eq [_ _ _ _] _ _ _ _ : clear implicits.

Eval compute in member_heq_eq (@MZ _ 1 nil) MZ eq_refl eq_refl.

Eval compute in member_heq_eq (@MN _ 2 1 (2 :: 3 :: nil) MZ) (MN MZ) eq_refl eq_refl.