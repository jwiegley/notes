Require Import Coq.Classes.SetoidClass.

Record SetoidObject := {
  carrier :> Set;
  is_setoid :> Setoid carrier
}.

Axiom nat_setoid : Setoid nat.

Canonical Structure setoidType (A : Set) `{S : Setoid A} : SetoidObject :=
  {| carrier := A; is_setoid := S |}.

Definition setoid_eq
           `{A : SetoidObject} (X : carrier A) (Y : carrier A) := X = Y.

Definition foo : Prop := setoid_eq 1 2.
