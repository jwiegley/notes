Require Import State SetLemmas Extras.

(************************************************************************)

Module Type StackSpec.
  Context {A : Type}.
  Parameter rep : Type.
  Definition DSL := @DSL rep.

  (* After the boilerplate above, what follows is the "spec interface". *)

  Parameter empty : Comp rep.
  Parameter push  : A -> DSL unit.
  Parameter pop   : DSL (option A).

  Open Scope state_scope.

  Axiom push_pop : forall x : A, push x >> pop ≈ return (Some x).
End StackSpec.

(************************************************************************)

Module StackDef <: StackSpec.
  Require Import Vectors.

  Context {A : Type}.
  Definition rep := { n : nat & Vec A n }.
  Definition DSL := @DSL rep.

  Definition empty : Comp rep := ret (existT _ 0 (vnil A)).

  Definition push (x : A) : DSL unit := fun r : rep =>
    match r with existT n v =>
      ret (existT _ (S n) (vcons x v), tt)
    end.

  Definition pop : DSL (option A) := fun r : rep =>
    match r with
      | existT O vnil => ret (r, None)
      | existT (S n) (x, v) => ret (existT _ n v, Some x)
    end.

  Open Scope state_scope.

  Theorem push_pop : forall x : A, push x >> pop ≈ return (Some x).
  Proof.
    intros ? [? ?].
    simplify with monad laws.
    reflexivity.
  Qed.
End StackDef.

(************************************************************************)

Module StackADT.
  Include StackDef.

  Definition spec : ADT _ := ADTRep rep {
    Def Constructor0 "new" : rep := empty,

    Def Method1 "push" (r : rep) (x : A) : rep * unit     := push x r,
    Def Method0 "pop"  (r : rep)         : rep * option A := pop r
  }%ADTParsing.
End StackADT.

(************************************************************************)

Module StackImpl.
  Include StackADT.

  Require Import Vectors.

  Definition VecAsList_AbsR (r_o : rep) (r_n : list A) :=
    match r_o with existT n v => vec_to_seq v = r_n end.

  Require Import
    Fiat.ADTRefinement
    Fiat.ADTRefinement.BuildADTRefinements.

  Theorem sharpened : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using VecAsList_AbsR.

    (* constructor: new *)
    {
      simplify with monad laws; simpl.
      refine pick val nil.
        finish honing.
      reflexivity.
    }

    (* method: push *)
    {
      unfold push.
      destruct r_o as [n v].
      simplify with monad laws; simpl.
      refine pick val (cons d r_n).
        simplify with monad laws; simpl.
        finish honing.
      destruct n as [|n]; simpl.
        destruct v; simpl.
        inversion H0; simpl.
        reflexivity.
      f_equal.
      apply H0.
    }

    (* method: pop *)
    {
      unfold pop.
      destruct r_o as [n v].
      unfold VecAsList_AbsR in H0.
      destruct_for_refine r_n; subst_evars.
        destruct n.
          simplify with monad laws; simpl.
          rewrite H0.
          refine pick eq.
          simplify with monad laws; simpl.
          reflexivity.
        destruct v as [x' v']; simpl;
        rewrite vec_seq_cons in H0.
        discriminate.
      destruct n.
        destruct v.
        simpl in H0.
        discriminate.
      destruct v as [x' v']; simpl;
      simplify with monad laws; simpl.
      rewrite vec_seq_cons in H0.
      inversion H0.
      rewrite H3.
      refine pick eq.
      simplify with monad laws; simpl.
      instantiate
        (1 := (fun (a : A) (l : seq A)
                   (_ : (fun _ : seq A => Comp (seq A * option A)) l) =>
                 ret (l, Some a))).
      reflexivity.
    }

    finish_SharpeningADT_WithoutDelegation.

    unfold ComputationalADT.LiftcMethod, ComputationalADT.LiftcMethod'.
  Defined.

  Time Definition impl := Eval simpl in (projT1 sharpened).
  Print impl.

  Require Import Coq.Strings.String.

  Open Scope string_scope.

  Definition newS  := "new".
  Definition pushS := "push".
  Definition popS  := "pop".

  Definition newStack : ComputationalADT.cRep impl :=
    Eval simpl in CallConstructor impl newS.
  Definition pushStack (r : ComputationalADT.cRep impl) (x : A) :
    ComputationalADT.cRep impl * unit :=
      Eval simpl in CallMethod impl pushS r x.
  Definition popStack (r : ComputationalADT.cRep impl) :
    ComputationalADT.cRep impl * option A :=
      Eval simpl in CallMethod impl popS r.

End StackImpl.

Extraction Language Haskell.

Module Import M := StackImpl.

Extraction "Stack.hs" newStack pushStack popStack.
