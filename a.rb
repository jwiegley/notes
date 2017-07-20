Require Export Program.
Require Export Coq.Arith.EqNat.
Require Export FMapInterface.
Require Export List.
Require Export Coq.FSets.FMapFacts.
Require Export Coq.FSets.FMapList.
Require Export Coq.Structures.DecidableTypeEx.

Set Implicit Arguments.

Module Type OptionalDecidableType.

  Parameter X : Type.
  Parameter o_eq_dec : option (forall (x y: X), {x = y} + {x <> y}).

End OptionalDecidableType.

Module FMapExpr (E:DecidableType) (Import M: WSfun E) (Import V:OptionalDecidableType).
  Module Export BasicMapFacts := WFacts_fun E M.
  Module Export BasicMapProperties := WProperties_fun E M.

  Definition Map : M.t V.X := M.empty V.X.

  Ltac cute_tactic :=
    match goal with
    | [ |- Empty (elt:=X) _] => apply M.is_empty_2
    end.

End FMapExpr.

Module MyDecidableType <: OptionalDecidableType.
  Definition X := nat.
  Definition o_eq_dec : option (forall (x y: X), {x = y} + {x <> y}).
    apply None.
  Defined.
End MyDecidableType.

Module Import F := FMapList.Make(Nat_as_DT).
Module Import M := FMapExpr Nat_as_DT F MyDecidableType.

(* This works, but only if my code is written in terms of [MyDecidableType.X]. *)
Goal Empty (elt:=MyDecidableType.X) Map.
cute_tactic.
Abort.

(* This does not work, because even though the types are the same up to
   I-forget-which-greek-letter equivalence, they no longer line up exactly
   enough for the tactics defined by [MyDecidableType].

   If the tactics had been defined over some family of type class instances,
   this would have been compatible with my own code specified using direct
   types, rather than indirecting through the module interface. *)
Goal Empty (elt:=nat) Map.
Fail cute_tactic.
Abort.