Class Product (C : Category) (P : C) `(p1 : P ~> X) `(p2 : P ~> Y) :=
{ product_ump :
    forall (Z : C) (x1 : Z ~> X) (x2 : Z ~> Y),
       exists (u : Z ~> P), x1 = p1 ∘ u /\ x2 = p2 ∘ u
    /\ forall (v : Z ~> P), p1 ∘ v = x1 /\ p2 ∘ v = x2 -> v = u
}.
