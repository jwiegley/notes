(* A reified arrow is a list of morphism indices within the current
   environment that denotes a known arrow. *)
Inductive ReifiedArrow (dom : obj_idx) : obj_idx -> list arr_idx -> Type :=
  | IdentityArrow : ReifiedArrow dom dom []
  | SingleArrow : forall (f : arr_idx) (cod : obj_idx)
                         (f' : objs dom ~> objs cod),
      arrs f = Some (dom; (cod; f'))
        -> ReifiedArrow dom cod [f]
  | ComposedArrow : forall (mid cod : obj_idx) f g gs,
      ReifiedArrow mid cod [f]
        -> ReifiedArrow dom mid (g :: gs)
        -> ReifiedArrow dom cod (f :: g :: gs).

Definition getArrList {dom cod} `(a : ReifiedArrow dom cod fs) :
  list arr_idx := fs.
Arguments getArrList {dom cod fs} a /.

Equations getArrMorph {dom cod fs} (a : ReifiedArrow dom cod fs) :
  objs dom ~{C}~> objs cod :=
  getArrMorph IdentityArrow := id;
  getArrMorph (SingleArrow f _) := f;
  getArrMorph (ComposedArrow f g) := getArrMorph f ∘ getArrMorph g.
