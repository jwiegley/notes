Require Import
  Coq.NArith.NArith
  Coq.Strings.Ascii
  Coq.Strings.String.

Generalizable All Variables.

Open Scope string_scope.
Open Scope list_scope.

Inductive term : Type :=
  | TChr : string -> term
  | TStr : string -> term
  | TInt : N -> term
  | TSym : string -> term
  | TCons : term -> term -> term.

Definition eval (env : unit) (t : term) : term :=
  match t with
  | TChr x => t
  | TStr x => t
  | TInt x => t
  | TSym x => t                 (* lookup variable value *)
  | TCons x y =>                (* lookup function value *)
  end.