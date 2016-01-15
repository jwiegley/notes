Definition find_P {A} (P : A -> Prop) (xs : list A)
  (x : A | List.In x xs /\ P x) : { x : A | P x } :=
  let (x0, a) := x in
  match a with
  | conj _ H0 => exist (fun x1 : A => P x1) x0 H0
  end.
