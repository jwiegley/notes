Definition surjective `(f : X -> Y) : Prop := forall y, exists x, f x = y.

Goal { n : nat | surjective (plus n) }.
Proof.
  exists 0.
  rewrite /surjective.
  move=> y.
  exists y.
  reflexivity.
Qed.
