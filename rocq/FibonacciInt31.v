Require Import Fiat.ADT Fiat.ADTNotation.

Module Type Number.
  Parameter N : Type.
  Parameter from_nat : nat -> N.
  Parameter to_nat : N -> nat.

  (* This axiom establishes the "meaning" of [from_nat] in relation to the
     subset of natural numbers it's capable of representing. *)
  Axiom from_to_nat : forall x : N, from_nat (to_nat x) = x.
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

(* This module extends Coq's int31 library with additional facts. *)
Module Int31Params <: Number.
  Require Export
    Coq.Numbers.Cyclic.Int31.Int31
    Coq.Numbers.Cyclic.Int31.Cyclic31.

  Lemma add31_O_n : forall n : int31, (0 + n)%int31 = n.
  Proof.
    induction n using int31_ind_sneakl.
      reflexivity.
    unfold add31.
    simpl.
    rewrite phi_inv_phi.
    reflexivity.
  Qed.

  Lemma add31_n_O : forall n : int31, (n + 0)%int31 = n.
  Proof.
    induction n using int31_ind_sneakl.
      reflexivity.
    unfold add31.
    simpl.
    replace (phi 0) with 0%Z; auto.
    rewrite Z.add_0_r.
    rewrite phi_inv_phi.
    reflexivity.
  Qed.

  Lemma add31c_O_n : forall n : int31, (0 +c n)%int31 = C0 n.
  Proof.
    intros.
    unfold add31c.
    rewrite add31_O_n.
    simpl.
    rewrite Zcompare.Zcompare_refl.
    reflexivity.
  Qed.

  Lemma add31_assoc x y z : (x + (y + z) = x + y + z)%int31.
  Proof.
    unfold add31.
    repeat rewrite phi_phi_inv.
    repeat rewrite <- spec_add.
  Admitted.

  Lemma add31_comm x y : (x + y = y + x)%int31.
  Proof.
    unfold add31.
    rewrite Z.add_comm.
    reflexivity.
  Qed.

  Lemma add31c_comm x y : (x +c y = y +c x)%int31.
  Proof.
    unfold add31c.
    rewrite add31_comm.
    rewrite Z.add_comm.
    reflexivity.
  Qed.

  Require Export Coq.Strings.String.
  Open Scope string_scope.

  Require Export QuickChick GenLow GenHigh.
  Open Scope Checker_scope.

  Definition digitsToHexNibble (d1 d2 d3 d4 : digits) : string :=
    match d1, d2, d3, d4 with
    | D0, D0, D0, D0 => "0"
    | D0, D0, D0, D1 => "1"
    | D0, D0, D1, D0 => "2"
    | D0, D0, D1, D1 => "3"
    | D0, D1, D0, D0 => "4"
    | D0, D1, D0, D1 => "5"
    | D0, D1, D1, D0 => "6"
    | D0, D1, D1, D1 => "7"
    | D1, D0, D0, D0 => "8"
    | D1, D0, D0, D1 => "9"
    | D1, D0, D1, D0 => "a"
    | D1, D0, D1, D1 => "b"
    | D1, D1, D0, D0 => "c"
    | D1, D1, D0, D1 => "d"
    | D1, D1, D1, D0 => "e"
    | D1, D1, D1, D1 => "f"
    end.

  Global Instance showInt31 : Show int31 := {|
    show t :=
      match t with
      I31     d1  d2  d3  d4  d5  d6  d7
          d8  d9  d10 d11 d12 d13 d14 d15
          d16 d17 d18 d19 d20 d21 d22 d23
          d24 d25 d26 d27 d28 d29 d30 d31 => "0x" ++
        digitsToHexNibble D0  d1  d2  d3  ++
        digitsToHexNibble d4  d5  d6  d7  ++
        digitsToHexNibble d8  d9  d10 d11 ++
        digitsToHexNibble d12 d13 d14 d15 ++
        digitsToHexNibble d16 d17 d18 d19 ++
        digitsToHexNibble d20 d21 d22 d23 ++
        digitsToHexNibble d26 d25 d26 d27 ++
        digitsToHexNibble d28 d29 d30 d31
      end
  |}.

  Notation "'do!' X <- A ; B" :=
    (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).

  Global Instance arbDigits : Arbitrary digits := {|
    arbitrary := do! b <- arbitrary;
                 returnGen (if b : bool then D0 else D1);
    shrink t := cons t nil
  |}.

  Global Instance arbInt31 : Arbitrary int31 := {|
    arbitrary :=
      do! d1  <- arbitrary;
      do! d2  <- arbitrary;
      do! d3  <- arbitrary;
      do! d4  <- arbitrary;
      do! d5  <- arbitrary;
      do! d6  <- arbitrary;
      do! d7  <- arbitrary;
      do! d8  <- arbitrary;
      do! d9  <- arbitrary;
      do! d10 <- arbitrary;
      do! d11 <- arbitrary;
      do! d12 <- arbitrary;
      do! d13 <- arbitrary;
      do! d14 <- arbitrary;
      do! d15 <- arbitrary;
      do! d16 <- arbitrary;
      do! d17 <- arbitrary;
      do! d18 <- arbitrary;
      do! d19 <- arbitrary;
      do! d20 <- arbitrary;
      do! d21 <- arbitrary;
      do! d22 <- arbitrary;
      do! d23 <- arbitrary;
      do! d24 <- arbitrary;
      do! d25 <- arbitrary;
      do! d26 <- arbitrary;
      do! d27 <- arbitrary;
      do! d28 <- arbitrary;
      do! d29 <- arbitrary;
      do! d30 <- arbitrary;
      do! d31 <- arbitrary;
      returnGen (I31     d1  d2  d3  d4  d5  d6  d7
                     d8  d9  d10 d11 d12 d13 d14 d15
                     d16 d17 d18 d19 d20 d21 d22 d23
                     d24 d25 d26 d27 d28 d29 d30 d31);
    shrink t := cons t nil
  |}.

  (* Carried numbers *)

  Definition carry_eqb31 (x y : carry int31) : bool :=
    match x, y with
    | C0 x, C0 y => eqb31 x y
    | C1 x, C1 y => eqb31 x y
    | _,    _    => false
    end.

  Definition carry_add (x y : carry int31) : carry int31 :=
    match x, y with
    | C0 x, C0 y => add31c x y
    | C0 x, C1 y => C1 (add31 x y)
    | C1 x, C0 y => C1 (add31 x y)
    | C1 x, C1 y => C1 (add31 x y)
    end.

  Lemma carry_add_comm x y : carry_add x y = carry_add y x.
  Proof.
    destruct x as [x|];
    destruct y as [y|]; simpl;
    try rewrite add31c_comm;
    try rewrite add31_comm;
    reflexivity.
  Qed.

  Lemma carry_add_assoc x y z :
    carry_add x (carry_add y z) = carry_add (carry_add x y) z.
  Proof.
    destruct x as [x|x];
    destruct y as [y|y];
    destruct z as [z|z];
    unfold carry_add; simpl;
    try (rewrite add31_assoc; reflexivity).
  Admitted.

  Global Instance showCarryInt31 : Show (carry int31) := {|
    show t := match t with
              | C0 x => show x
              | C1 y => "!" ++ show y
              end
  |}.

  Global Instance arbCarry {A} `{Arbitrary A} : Arbitrary (carry A) := {|
    arbitrary := do! b <- arbitrary;
                 liftGen ((if b : bool then @C0 else @C1) A) arbitrary;
    shrink t := cons t nil
  |}.

  Definition carry_add_assoc_test : Checker :=
    forAll arbitrary (fun x =>
    forAll arbitrary (fun y =>
    forAll arbitrary (fun z =>
      carry_eqb31 (carry_add x (carry_add y z))
                  (carry_add (carry_add x y) z)))).

  QuickChick carry_add_assoc_test.

  (* Define what is needed to satisfy [Number]. *)

  Definition N := carry int31.

  (* Although this function looks horrible from a computational perspective,
     it's only need to verify our abstraction relation below. It is not used
     by the final extracted code, which only uses carried int31 values. *)
  Fixpoint from_nat (n : nat) : carry int31 :=
    match n with
    | O   => C0 On
    | S x => carry_add (C0 In) (from_nat x)
    end.

  Definition int31_to_nat : int31 -> nat :=
    recr nat 0 (fun b _ => match b with
                           | D0 => Div2.double
                           | D1 => compose S Div2.double
                           end).

  Definition to_nat (n : carry int31) : nat :=
    match n with
    | C0 x => int31_to_nat x
    | C1 y => int31_to_nat y + NPeano.pow 2 size
    end.

  Lemma carry_add_one (x : nat) :
    from_nat (S x) = carry_add (from_nat 1) (from_nat x).
  Proof.
    simpl.
    rewrite add31_n_O.
    reflexivity.
  Qed.

  Theorem carry_add_distr : forall x y : nat,
    from_nat (x + y) = carry_add (from_nat x) (from_nat y).
  Proof.
    intro x.
    induction x as [|x' IHx]; intros.
      simpl.
      destruct (from_nat y); auto.
        rewrite add31c_O_n.
        reflexivity.
      rewrite add31_O_n.
      reflexivity.
    rewrite plus_Snm_nSm.
    rewrite IHx; clear IHx.
    rewrite carry_add_comm.
    replace (from_nat (S y))  with (carry_add (from_nat 1) (from_nat y)).
      replace (from_nat (S x')) with (carry_add (from_nat 1) (from_nat x')).
        rewrite <- carry_add_assoc.
        rewrite <- carry_add_assoc.
        f_equal.
        apply carry_add_comm.
      apply carry_add_one.
    apply carry_add_one.
  Qed.

  Theorem from_to_nat : forall x : carry int31, from_nat (to_nat x) = x.
  Proof.
    destruct x as [x'|x'] eqn:Heqe; unfold to_nat.
  Admitted.

  Definition from_to_nat_test : Checker :=
    forAll arbitrary (fun x =>
      match x with
      | C0 y => match (y ?= 20000)%int31 with
                | Lt => carry_eqb31 (from_nat (to_nat x)) x
                | _ => true
                end
      | _ => true
      end).

  QuickChick from_to_nat_test.
End Int31Params.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

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
      refine pick val (C0 On, C0 In).
        finish honing.
      split; auto.
    }

    (* method: next *)
    {
      unfold NatAsInt_AbsR in *.
      destruct r_o as [o1 o2].
      simplify with monad laws; simpl.
      inversion H0; clear H0; simpl in *.
      refine pick val (snd r_n, carry_add (fst r_n) (snd r_n)).
        simplify with monad laws.
        rewrite carry_add_distr.
        rewrite H1.
        rewrite H2.
        finish honing.
      intuition.
      rewrite <- H1.
      rewrite <- H2.
      apply carry_add_distr.
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

Section Direct.
  Fixpoint Fibonacci (n : nat) : nat :=
    match n with
    | 0 => 0
    | S n' =>
      match n' with
      | 0 => 1
      | S n'' => Fibonacci n' + Fibonacci n''
      end
    end.

  Definition FibonacciComp : constructorType nat [nat : Type] :=
    fun n => ret (Fibonacci n).

  Definition refined_Fibonacci :
    { T : Type &
    { AbsR : nat -> T -> Prop &
    { fib_new : constructorType T [nat : Type] &
      refineConstructor AbsR FibonacciComp fib_new } } }.
  Proof.
    do 3 eexists.
    (* We can do etransitivity to make small steps. *)
    eapply refineConstructor_trans.
    Undo.
    (* The easiest abstraction relation is equality. *)
    instantiate (2 := eq).
    unfold refineConstructor; intros.
    finish honing.
    (* But you probably want something else. *)
    Undo 3.
    (* This means you can get unexpected results though. *)
    instantiate (2 := fun _ (x : nat) => True).
    unfold refineConstructor.
    intros; instantiate (1 := fun n : nat => ret (2 * n)).
    simplify with monad laws; simpl.
    refine pick val _.
    finish honing.
    intuition.
  Defined.

  Time Definition impl :=
    Eval simpl in (projT1 (projT2 (projT2 refined_Fibonacci))).
  Print impl.
End Direct.

Extraction Language Haskell.

Import Fib.

Print Assumptions newFib.
Print Assumptions nextFib.

Extraction "Fibonacci.hs" newFib nextFib.
