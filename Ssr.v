Require Import Hask.Prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Variable a : Set.
Variable P : a -> Prop.

Record RType : Type := {
    someData : a;
    _        : P someData
}.

Inductive IType := MkI : forall x: a, P x -> IType.

Definition SType := { x : a | P x }.
