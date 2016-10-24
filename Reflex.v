Require Import Fiat.ADT Fiat.ADTNotation.

Require Import
  Coq.Strings.String
  Coq.NArith.NArith
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Open Scope string_scope.
Open Scope N_scope.

Definition newNetwork := "newNetwork".
Definition constant   := "constant".

Module ReflexFRP (M : WSfun N_as_DT).

Inductive Time :=.

Program Definition Network := Def ADT {
  rep := _,

  Def Constructor0 newNetwork : rep := ret _,,

  Def Method1 constant (r : rep) _ : rep * _ :=
    ret ((fst r + 1, , 0)
}.
Obligation 1.
  exists 0%nat.
  exists (Vector.nil _).
  exact inil.
Defined.