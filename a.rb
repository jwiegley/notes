Equations ReifiedArrow_comp {dom mid cod}
          `(f : ReifiedArrow mid cod (x :: xs))
          `(g : ReifiedArrow dom mid (y :: ys)) :
  ReifiedArrow dom cod (x :: xs ++ y :: ys) :=
  ReifiedArrow_comp (SingleArrow a _ a' f) g :=
    ComposedArrow _ _ _ _ _ _ (SingleArrow _ a _ a' f) g;
  ReifiedArrow_comp (ComposedArrow f g) h :=
    ComposedArrow _ _ _ _ _ _ f (ReifiedArrow_comp g h).
