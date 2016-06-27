Require Import NArith.
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

Definition Vector_eq_dec `(eq_dec : forall x y : A, {x = y} + {x <> y}) :
  forall (n : nat) (l l' : Vector.t A n), {l = l'} + {l <> l'}.
Proof.
  Require Import Coq.Program.Equality.
  induction l; simpl;
  dependent destruction l'.
    left; reflexivity.
  destruct (eq_dec h h0);
  destruct (IHl l').
  - rewrite e, e0.
    left; reflexivity.
  - rewrite e.
    right.
    unfold not; intros.
    inversion H.
    simpl_existT.
    contradiction.
  - rewrite e.
    right.
    unfold not; intros.
    inversion H.
    contradiction.
  - right.
    unfold not; intros.
    inversion H.
    contradiction.
Defined.

Module Sums.
  Record NamedSum (sumIdent : string) : Set := {
    sumCard  : nat;
    sumNames : Vector.t string sumCard;
    sumMuls  : Vector.t N sumCard
  }.

  Program Definition NamedSum_beq (s : string) (x y : NamedSum s) : bool :=
    match x, y with
      {| sumCard  := xsc
       ; sumNames := xsn
       ; sumMuls  := xsm |},
      {| sumCard  := ysc
       ; sumNames := ysn
       ; sumMuls  := ysm |} =>
      (beq_nat xsc ysc &&
       Sumbool.bool_of_sumbool
         (List.list_eq_dec string_dec (to_list xsn) (to_list ysn)) &&
       Sumbool.bool_of_sumbool
         (List.list_eq_dec N.eq_dec (to_list xsm) (to_list ysm)))%bool
    end.

  Definition NamedSum_eq_dec (s : string) (x y : NamedSum s) : {x=y} + {x<>y}.
  Proof.
    Import EqNotations.
    destruct x, y.
    destruct (eq_nat_dec sumCard0 sumCard1); subst.
      destruct (Vector_eq_dec string_dec sumCard1 sumNames0 sumNames1).
        destruct (Vector_eq_dec N.eq_dec sumCard1 sumMuls0 sumMuls1).
          left.
          rewrite e, e0.
          reflexivity.
        right.
        unfold not; intros.
        inversion H.
        apply EqdepFacts.eq_sigT_sig_eq in H1; destruct H1.
        apply EqdepFacts.eq_sigT_sig_eq in H2; destruct H2.
        simpl_eq.
        contradiction.
      right.
      unfold not; intros.
      inversion H.
      apply EqdepFacts.eq_sigT_sig_eq in H1; destruct H1.
      simpl_eq.
      contradiction.
    right.
    unfold not; intros.
    inversion H.
    contradiction.
  Defined.

  Open Scope string_scope.

  Definition distanceS := "distance".
  Definition timeS     := "time".

  Import VectorNotations.

  Definition Distance : NamedSum distanceS :=
    {| sumCard  := 2
     ; sumNames := ["meters"; "kilometers"]
     ; sumMuls  := [1%N; 1000%N] |}.

  Definition Time : NamedSum timeS :=
    {| sumCard  := 4
     ; sumNames := ["seconds"; "minutes"; "hours"; "days"]
     ; sumMuls  := [1%N; 60%N; 3600%N; 86400%N] |}.
End Sums.

Module Type Floats.
  Parameter M : Type.

  Parameter promote  : nat -> M.
  Parameter equalb   : M -> M -> bool.
  Parameter lesseqb  : M -> M -> bool.
  Parameter lessb    : M -> M -> bool.
  Parameter plus     : M -> M -> M.
  Parameter zero     : M.
  Parameter minus    : M -> M -> M.
  Parameter div      : M -> M -> option M.
  Parameter div_safe : M -> forall x : M, equalb x zero = false -> M.
  Parameter mult     : M -> M -> M.
  Parameter one      : M.

  Hypothesis plus_left_unit  : forall x, plus zero x = x.
  Hypothesis plus_right_unit : forall x, plus x zero = x.
  Hypothesis plus_assoc : forall x y z, plus x (plus y z) = plus (plus x y) z.

  Hypothesis mult_left_unit  : forall x, mult one x = x.
  Hypothesis mult_right_unit : forall x, mult x one = x.
  Hypothesis mult_assoc : forall x y z, mult x (mult y z) = mult (mult x y) z.
End Floats.

Module Units (M : Floats).
  Import M.
  Import Sums.

  Delimit Scope M_scope with M.

  Infix "*" := mult : M_scope.
  Infix "/" := div  : M_scope.

  Open Scope M_scope.

  Inductive UnitType : Type :=
    | TVal : forall s : string, NamedSum s -> UnitType
    | TMul : UnitType -> UnitType -> UnitType
    | TDiv : UnitType -> UnitType -> UnitType.

  Hint Constructors Vector.In.

  Inductive EVal {s : string} {n : NamedSum s} :=
    UVal : forall (u : string), Vector.In u (sumNames _ n) -> EVal.
  Inductive EMul {U T : Type} := UMul : U -> T -> EMul.
  Inductive EDiv {U T : Type} := UDiv : U -> T -> EDiv.

  Definition UnitExpr : UnitType -> Type :=
    fix typ ut := match ut return Type with
                  | TVal s n => @EVal s n
                  | TMul U T => @EMul (typ U) (typ T)
                  | TDiv U T => @EDiv (typ U) (typ T)
                  end.

  Delimit Scope T_scope with T.
  Bind Scope T_scope with UnitType.

  Notation "! U" := (TVal _ U) (at level 30) : T_scope.
  Infix "*" := TMul : T_scope.
  Infix "/" := TDiv : T_scope.

  Delimit Scope U_scope with U.
  Bind Scope U_scope with UnitExpr.

  Notation "! U" := (UVal U _) (at level 30) : U_scope.
  Infix "*" := UMul : U_scope.
  Infix "/" := UDiv : U_scope.

  Record Units (U : UnitType) := {
    value : M;
    units : UnitExpr U
  }.

  Arguments value {U} u.
  Arguments units {U} u.

  Notation "<< X | Y >>" := {| value := X; units := Y%U |}.

  Program Definition example_value : Units (!Distance / !Time)%T :=
    << promote 15 | !"meters"/!"seconds" >>.

  (* jww (2016-04-14): NYI *)
  Definition normalize_units {U} (x y : Units U) : Units U * Units U :=
    match x, y with
      {| value := vx; units := ux |},
      {| value := vy; units := uy |} => (x, y)
    end.

  (* jww (2016-04-14): NYI *)
  Definition compare_and_normalize_units {U T} (x : Units U) (y : Units T) :
    option (Units U * Units T) :=
    match x, y with
      {| value := vx; units := ux |},
      {| value := vy; units := uy |} => Some (x, y)
    end.

  Definition equalb_units {U} (x y : Units U) : bool :=
    match normalize_units x y with
      (x', y') => equalb (value x') (value y')
    end.

  Definition lesseqb_units {U} (x y : Units U) : bool :=
    match normalize_units x y with
      (x', y') => lesseqb (value x') (value y')
    end.

  Definition lessb_units {U} (x y : Units U) : bool :=
    match normalize_units x y with
      (x', y') => lessb (value x') (value y')
    end.

  Definition plus_units `{Convertible U} (x y : Units U) : Units U :=
    match normalize_units x y with
      (x', y') => {| value := plus (value x') (value y')
                   ; units := units x' |}
    end.

  Definition minus_units `{Convertible U} (x y : Units U) : Units U :=
    match normalize_units x y with
      (x', y') => {| value := minus (value x') (value y')
                   ; units := units x' |}
    end.

  Program Definition multiplied (U T : UnitType) :
    { W : UnitType & Units U -> Units T -> Units W } :=
    _.
  Obligation 1.
  Admitted.

  Program Definition mult_units `(x : Units U) `(y : Units T) :
    Units (projT1 (multiplied U T)) := projT2 (multiplied U T) x y.

  Program Definition divided (U T : UnitType) :
    { W : UnitType & Units U -> Units T -> option (Units W) } :=
    _.
  Obligation 1.
  Admitted.

  Program Definition div_units `(x : Units U) `(y : Units T) :
    option (Units (projT1 (divided U T))) := projT2 (divided U T) x y.

End Units.

Module Measures (U : Floats).
  Include (Units U).

  Record Measure := {
    probe : 

End Measures.