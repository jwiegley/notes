1 subgoal (ID 1072)
  
  H : Env
  x0, x1 : arr_idx num_arrs
  e2 : snd tys[@x0] = snd tys[@x1]
  ============================
  term_indices
    match
      match e2 in (_ = y) return (y = snd tys[@x0]) with
      | eq_refl => eq_refl
      end in (_ = y) return (Term tys (fst tys[@x1]) y)
    with
    | eq_refl => Morph x1
    end = [x1]%list
