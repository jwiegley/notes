Require Import Fiat.ADT Fiat.ADTNotation.

Module Type Number.
  Parameter N : Type.
  Parameter N_zero : N.
  Parameter N_one : N.
  Parameter N_plus : N -> N -> N.
  Parameter N_plus_within_bound : N * N -> bool.
  Axiom N_plus_zero_one : N_plus_within_bound (N_zero, N_one) = true.
End Number.

Module FibonacciBounded (Import M : Number).
  Definition spec : ADT _ := ADTRep (N * N) {
    Def Constructor0 "new" : rep :=
      ret (N_zero, N_one),

    Def Method0 "next" (r : rep) : rep * N :=
      If N_plus_within_bound r
      Then ret ((snd r, N_plus (fst r) (snd r)), fst r)
      Else ret ((N_one, N_one), N_zero)
  }%ADTParsing.

End FibonacciBounded.

Module Int31Params.
  Require Import Coq.Numbers.Cyclic.Int31.Int31 Coq.Arith.Div2.

  Definition N := int31.

  Definition N_zero := On.
  Definition N_one := In.

  Definition N_plus := add31.
  Definition N_plus_within_bound (p : N * N) : bool :=
    match add31c (fst p) (snd p) with
      | C1 _ => true
      | C0 z => match compare31 z Tn with
                | Eq => true
                | Lt => true
                | Gt => false
                end
    end.

  Theorem N_plus_zero_one : N_plus_within_bound (N_zero, N_one).
  Proof. reflexivity. Qed.
End Int31Params.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Module Fib.
  Module Import F := FibonacciBounded(Int31Params).
  Import Int31Params.

  Theorem sharpened : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using eq.

    (* constructor: new *)
    {
      simplify with monad laws.
      refine pick val (N_zero, N_one).
        finish honing.
      split; simpl;
      apply N_plus_zero_one.
    }

    (* method: next *)
    {
      rewrite H0; clear H0.
      rewrite refine_If_Then_Else_ret.
      simplify with monad laws; simpl.
      refine pick val (if N_plus_within_bound r_n
                       then (snd r_n, N_plus (fst r_n) (snd r_n))
                       else (N_one, N_one)).
        simplify with monad laws; simpl.
        finish honing.
      destruct (N_plus_within_bound r_n); auto.
    }

    finish_SharpeningADT_WithoutDelegation.
  Defined.

  Time Definition impl := Eval simpl in (projT1 sharpened).
  Print impl.

  Require Import Coq.Strings.String.
  Open Scope string_scope.

  Definition newS  := "new".
  Definition nextS := "next".

  Definition newFib : ComputationalADT.cRep impl :=
    Eval simpl in CallConstructor impl newS.
  Definition nextFib (r : ComputationalADT.cRep impl) :
    ComputationalADT.cRep impl * N :=
      Eval simpl in CallMethod impl nextS r.
End Fib.

Extraction Language Haskell.

Import Fib.

Print Assumptions newFib.
Print Assumptions nextFib.

Extraction "FibonacciBounded.hs" newFib nextFib.
