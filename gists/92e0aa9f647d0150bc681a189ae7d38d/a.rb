Inductive ValidArrow (dom : obj_idx) : obj_idx -> list arr_idx -> Type :=
  | IdentityArrow : ValidArrow dom dom []
  | ComposedArrow : forall mid cod f f' gs,
      arrs f = Some (mid; (cod; f'))
        -> ValidArrow dom mid gs
        -> ValidArrow dom cod (f :: gs).

Equations ValidArrow_eq_equiv {dom cod fs}
          (f g : ValidArrow dom cod fs) : { f = g } + { f ≠ g } :=
  ValidArrow_eq_equiv IdentityArrow IdentityArrow := left eq_refl;
  ValidArrow_eq_equiv (ComposedArrow midf codf _ _ _ _ IHf)
                      (ComposedArrow ?(midf) ?(codf) _ _ _ _ IHg) :=
    _ (ValidArrow_eq_equiv IHf IHg).
