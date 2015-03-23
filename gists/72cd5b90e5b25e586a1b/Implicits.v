Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
  | Unknown : maybe P
  | Found : forall x : A, P x -> maybe P.

Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Definition neat (x : nat) : Prop := True.
Definition neatO : neat 0 := I.
Definition foo : maybe (fun (x : nat) => True) := Found neatO.