1 subgoal (ID 2487)
  
  H : Env
  dom : obj_idx
  f : arr_idx num_arrs
  f0 : Arrows tys dom (fst tys[@f])
  g : Arrows tys dom (snd tys[@f])
  IHf : ∀ g : Arrows tys dom (fst tys[@f]), f0 = g ∨ f0 ≠ g
  ============================
  Arr f f0 = g ∨ Arr f f0 ≠ g
