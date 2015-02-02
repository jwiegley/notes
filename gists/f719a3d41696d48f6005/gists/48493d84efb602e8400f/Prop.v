Inductive pal (X : Type) : list X -> Prop :=
  | pal_nil : pal X []
  | pal_one x : pal X [x]
  | pal_xs x xs : pal X xs -> pal X (x :: snoc xs x).
