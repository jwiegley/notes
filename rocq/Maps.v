Require Import
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx
  PeanoNat.

Module Import M := FMapAVL.Make(Nat_as_OT).

Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Compute M.find 1 (M.add 1 10 (M.empty _)).
Compute P.for_all (fun k _ => k <? 10) (M.add 1 10 (M.empty _)).
