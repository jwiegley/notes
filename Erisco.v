Require Import Fiat.ADT Coq.Strings.String.

Open Scope string_scope.

Definition foo (x : nat) (s : string) : Comp nat :=
  b <- { b : bool | s = "Hello" };
  if b
  then { n : nat | n < x }
  else ret (length s).