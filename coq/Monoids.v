Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Tactics.

Reserved Infix "⊗" (at level 39, right associativity).

Class Monoid := {
    carrier : Set;
    mempty : carrier;
    mappend : carrier → carrier → carrier where "x ⊗ y" := (mappend x y);

    left_id : ∀ x, mempty ⊗ x = x;
    right_id : ∀ x, x ⊗ mempty = x;
    assoc : ∀ x y z, (x ⊗ y) ⊗ z = x ⊗ (y ⊗ z)
}.

class (Monoid a, Monoid b) => Profunctor m a b where
  dimap :: (b -> a) -> (c -> d) -> m a c -> m b d