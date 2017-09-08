


  | One'    : ∀ {a}, Hom a One_

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b
  | Fork    : ∀ {a c d}, Hom a c -> Hom a d -> Hom a (Prod_ c d)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c -> Hom a (Exp_ b c)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) -> Hom (Prod_ a b) c

  | Zero'   : ∀ {a}, Hom Zero_ a

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)
  | Merge   : ∀ {a c d}, Hom c a -> Hom d a -> Hom (Coprod_ c d) a
  with
Hosted (r obj : Type) := Embed : Hom r obj -> Hosted r obj.

Program Fixpoint interp `(c : Hom a b) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
  match c with
  | Id          => id
  | Compose f g => interp f ∘ interp g

  | One'        => one

  | Exl         => exl
  | Exr         => exr
  | Fork f g    => fork (interp f) (interp g)

  | Curry f     => curry (interp f)
  | Uncurry f   => uncurry (interp f)

  | Zero'       => zero

  | Inl         => inl
  | Inr         => inr
  | Merge f g   => merge (interp f) (interp g)
  end.

Program Instance AST : Category := {
  obj     := Obj;
  hom     := Hom;
  id      := @Id;
  compose := @Compose;
  homset  := fun _ _ =>
    {| equiv := fun f g =>
         forall {C : Category}
                {A : @Cartesian C}
                `{@Closed C A}
                `{@Cocartesian C}
                `{@Terminal C}
                `{@Initial C},
           interp f ≈ interp g |}
}.
Next Obligation.
  equivalence.
  transitivity (interp y); auto.
Qed.

Program Instance Hom_Terminal : @Terminal AST := {
  terminal_obj := One_;
  one := @One'
}.

Program Instance Hom_Cartesian : @Cartesian AST := {
  product_obj := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [? ?].
  rewrite <- e, <- e0.
  rewrite fork_comp; cat.
Qed.

Program Instance Hom_Closed : @Closed AST _ := {
  exponent_obj := Exp_;
  exp_iso := fun x y z =>
    {| to   := {| morphism := @Curry x y z |}
     ; from := {| morphism := @Uncurry x y z |} |}
}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.

Program Instance Hom_Initial : @Initial AST := {
  terminal_obj := Zero_;
  one := @Zero'
}.

Program Instance Hom_Cocartesian : @Cocartesian AST := {
  product_obj := Coprod_;
  fork := @Merge;
  exl  := @Inl;
  exr  := @Inr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [? ?].
  rewrite <- e, <- e0.
  rewrite merge_comp; cat.
Qed.

Program Instance interp_proper {x y : Obj}
        {C : Category} {A : @Cartesian C}
        `{@Closed C A} `{@Cocartesian C}
        `{@Terminal C} `{@Initial C} :
  Proper (@equiv _ (@homset AST x y) ==>
                     @equiv _ (@homset C _ _))
         (fun f => @interp x y f C A _ _ _ _).

Require Export Category.Functor.Structure.Terminal.
Require Export Category.Functor.Structure.Cartesian.
Require Export Category.Functor.Structure.Closed.

Section AST.

Context {C : Category}.
Context {A : @Cartesian C}.
Context `{@Closed C A}.
Context `{@Cocartesian C}.
Context `{@Terminal C}.
Context `{@Initial C}.

Global Program Instance AST_Functor : AST ⟶ C := {
  fobj := fun x => denote x;
  fmap := fun _ _ f => interp f
}.

Global Program Instance Hom_TerminalFunctor : TerminalFunctor := {
  map_one := id
}.

Global Program Instance Hom_CartesianFunctor : CartesianFunctor := {
  fobj_prod_iso := _
}.

Global Program Instance Hom_ClosedFunctor : ClosedFunctor := {
  fobj_exp_iso := _
}.

Global Program Instance Hom_InitialFunctor : InitialFunctor AST_Functor := {
  map_one := id
}.

Global Program Instance Hom_CocartesianFunctor : CocartesianFunctor AST_Functor := {
  fobj_prod_iso := _
}.

End AST.
