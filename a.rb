Equations ReifiedArrow_comp_ex {dom mid cod}
          (f : ∃ xs, ReifiedArrow mid cod xs)
          (g : ∃ xs, ReifiedArrow dom mid xs) :
  ∃ xs, ReifiedArrow dom cod xs :=
  ReifiedArrow_comp_ex (existT _ IdentityArrow) g := g;
  ReifiedArrow_comp_ex f (existT _ IdentityArrow) := f;
  ReifiedArrow_comp_ex (existT (SingleArrow a _ a' f)) (existT g) :=
    (_; ComposedArrow _ _ _ _ _ _ (SingleArrow _ a _ a' f) g);
  ReifiedArrow_comp_ex (existT (ComposedArrow f g)) (existT h) :=
    (_; ComposedArrow _ _ _ _ _ _ f (ReifiedArrow_comp g h)).
