Inductive Arrows {a} (tys : Vector.t (obj_idx * obj_idx) a) :
  obj_idx -> obj_idx -> Type :=
  | Nil : ∀ dom, Arrows tys dom dom
  | Arr dom (f : arr_idx a) :
      Arrows tys dom (fst (tys[@f])) ->
      Arrows tys dom (snd (tys[@f])).

Arguments Nil {a tys dom}.
Arguments Arr {a tys dom} _ _.

Equations Arrows_eq_dec {d c} (f g : Arrows tys d c) : {f = g} + {f ≠ g} :=
  Arrows_eq_dec Nil Nil := in_left;
  Arrows_eq_dec (Arr x xs) (Arr y ys) <= eq_dec x y => {
    | in_left <= Arrows_eq_dec xs ys => {
        | in_left => in_left;
        | _ => in_right
      };
    | _ => in_right
  };
  Arrows_eq_dec _ _ := in_right.
