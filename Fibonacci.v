Require Import Fiat.ADT Fiat.ADTNotation.

Module Type Number.
  Parameter N : Type.
  Parameter from_nat : nat -> N.
End Number.

Module Fibonacci (Import M : Number).

  Definition spec : ADT _ := ADTRep (nat * nat) {
    Def Constructor0 "new" : rep := ret (0, 1),
    Def Method0 "next" (r : rep) : rep * N :=
      match r with
        (r1, r2) => ret ((r2, r1 + r2), from_nat (r1 + r2))
      end
  }%ADTParsing.

End Fibonacci.

Module Int31Params <: Number.
  Require Export
    Coq.Numbers.Cyclic.Int31.Int31
    Coq.Numbers.Cyclic.Int31.Cyclic31
    Coq.Arith.Div2.

  Definition N := carry int31.

  Definition carry_add (x y : carry int31) : carry int31 :=
    match x, y with
    | C0 x', C0 y' => add31c x' y'
    | C1 x', C0 y' => C1 (add31 x' y')
    | C0 x', C1 y' => C1 (add31 x' y')
    | C1 x', C1 y' => C1 (add31 x' y')
    end.

  Fixpoint from_nat (p : nat) : carry int31 :=
    match p with
    | O   => C0 On
    | S n => carry_add (C0 In) (from_nat n)
    end.

  Definition N_plus := add31.

  Lemma add31_On (x : int31) :
    add31 On x = x.
  Proof.
    unfold add31.
    simpl.
    apply phi_inv_phi.
  Qed.

  Lemma add31c_On (x : int31) :
    add31c On x = C0 x.
  Proof.
    unfold add31c.
    rewrite add31_On.
    simpl.
    rewrite Zcompare.Zcompare_refl.
    reflexivity.
  Qed.

  Theorem from_nat_plus_one x :
    from_nat (S x) = carry_add (C0 In) (from_nat x).
  Proof. destruct x; auto. Qed.

  Theorem carry_add_assoc x y z :
    carry_add x (carry_add y z) = carry_add (carry_add x y) z.
  Proof.
    unfold carry_add.
    destruct x as [x|x]; destruct y as [y|y]; destruct z as [z|z].
  Admitted.

  Theorem N_plus_distr : forall x y : nat,
    from_nat (x + y) = carry_add (from_nat x) (from_nat y).
  Proof.
    intros.
    induction x as [|x' IHx].
      simpl.
      destruct (from_nat y).
        rewrite add31c_On.
        reflexivity.
      rewrite add31_On.
      reflexivity.
    rewrite from_nat_plus_one.
    rewrite <- carry_add_assoc.
    rewrite <- IHx.
    rewrite <- from_nat_plus_one.
    rewrite <- plus_Sn_m.
    reflexivity.
  Qed.
End Int31Params.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Ltac skip_with_existential :=
  match goal with |- ?G =>
    let H := fresh in evar(H:G); eexact H end.

Module F := Fibonacci(Int31Params).

Module Fib.
  Import F.
  Import Int31Params.

  Definition NatAsInt_AbsR (r_o : nat * nat)
                           (r_n : carry int31 * carry int31) :=
    from_nat (fst r_o) = fst r_n /\ from_nat (snd r_o) = snd r_n.

  Theorem sharpened : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using NatAsInt_AbsR.

    (* constructor: new *)
    {
      simplify with monad laws.
      refine pick val ((C0 On, C0 In)).
        finish honing.
      split; auto.
    }

    (* method: next *)
    {
      unfold NatAsInt_AbsR in *.
      destruct r_o as [o1 o2].
      simplify with monad laws; simpl.
      refine pick val (snd r_n, carry_add (fst r_n) (snd r_n)).
        simplify with monad laws.
        inversion H0; clear H0; simpl in *.
        rewrite N_plus_distr.
        rewrite H1.
        rewrite H2.
        finish honing.
      simpl in *.
      inversion H0; clear H0.
      intuition.
      rewrite <- H1.
      rewrite <- H2.
      apply N_plus_distr.
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
    ComputationalADT.cRep impl * carry int31 :=
      Eval simpl in CallMethod impl nextS r.
End Fib.

Extraction Language Haskell.

Import Fib.

Print Assumptions newFib.
Print Assumptions nextFib.

Extraction "Fibonacci.hs" newFib nextFib.
