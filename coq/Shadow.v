Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Construction.Coproduct.

Class Shadowed (rich weak : Type) := {
  forget : rich -> weak;
  embed  : weak -> option rich;

  forget_embed : ∀ x, embed (forget x) = Some x;
  embed_forget : ∀ x y, embed x = Some y -> forget y = x
}.
