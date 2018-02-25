Equations ReifiedArrow_getArrMorph_comp {dom mid cod}
          `(f : ReifiedArrow mid cod (x :: xs))
          `(g : ReifiedArrow dom mid (y :: ys)) :
  getArrMorph (ReifiedArrow_comp f g) ≈ getArrMorph f ∘ getArrMorph g :=
  ReifiedArrow_getArrMorph_comp f g by rec xs (MR lt (@length arr_idx)) :=
  ReifiedArrow_getArrMorph_comp SingleArrow g := reflexivity _;
  ReifiedArrow_getArrMorph_comp (ComposedArrow f f') g := _.
Next Obligation.
  rewrite ReifiedArrow_comp_equation_2.
  rewrite !getArrMorph_equation_3.
  rewrite ReifiedArrow_getArrMorph_comp; cat.
  constructor.
Defined.
