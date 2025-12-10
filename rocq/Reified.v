Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.BiCCC.

Require Import Coq.Vectors.Vector.
Import Vectors.VectorDef.VectorNotations.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Inductive IFree {A : Type} (f : A -> A -> Type -> Type) :
  A -> A -> Type -> Type :=
  | IPure : ∀ (i : A) (a : Type), a -> IFree f i i a
  | IJoin : ∀ (i j k : A) (a x : Type),
      (x -> IFree f j k a) -> f i j x -> IFree f i k a.

Arguments IPure {A f i a} _.
Arguments IJoin {A f i j k a x} _ _.

Definition liftF {A : Type} {f : A -> A -> Type -> Type} {a b : A} {x : Type} :
  f a b x -> IFree f a b x := IJoin IPure.

Inductive Sum {A : Type} (f g : A -> A -> Type -> Type)
          (i j : A) (a : Type) : Type :=
  | Inl : f i j a -> Sum f g i j a
  | Inr : g i j a -> Sum f g i j a.

Arguments Inl {A f g i j a} _.
Arguments Inr {A f g i j a} _.

Infix ":+:" := Sum (right associativity, at level 100).

Section HomF.

Context {C : Category}.

Inductive VoidF : C -> C -> Type -> Type :=
  | Void : ∀ a b r, False -> VoidF a b r.

(** [MorF] represents the base case for the least fixed-point of our F-Algebra
    describing morphisms in some category characterized by [obj] and [arr]. It
 ignores its [r] argument because it is not recursive. *)
Inductive MorF : C -> C -> Type -> Type :=
  | Morph : ∀ {a b : C} r, a ~> b -> MorF a b r.

(** Basic categorical structure is given by [HomF], which allows for identity
    and composition. *)
Inductive HomF : C -> C -> Type -> Type :=
  | Id      : ∀ {a     : C} r, HomF a a r
  | Compose : ∀ {a b c : C} r, r b c -> r a b -> HomF a c r.

End HomF.

(* Inductive FunF : forall (C : Category) (r : C -> C -> Type), C -> C -> Type := *)
(*   | Fmap : ∀ (C D : Category) {a b : D} (F : D ⟶ C) (r : D -> D -> Type), *)
(*       r a b -> FunF C (fun x y => r (F x) (F y)) (F a) (F b). *)

Section Hom.

Context {C : Category}.

Variable g : (C → C → Type -> Type) → C → C → Type -> Type.

(* Definition all := MorF :+: HomF :+: g. *)

Definition Hom (a b : C) : Type := IFree MorF a b.

Definition morph `(f : a ~> b) : Hom a b :=
  mkFix a b (fun _ _ => False) (False_rect _)
        (Inl (Morph (fun _ _ => False) f)).

Program Definition ident {a : C} : Hom a a :=
  mkFix a a (fun _ _ => False) (False_rect _) (Inr (Inl (Id _))).

Definition composed `(f : Hom b c) `(h : Hom a b) : Hom a c :=
  mkFix a c (Fix (MorF :+: HomF :+: g)) Datatypes.id
        (Inr (Inl (Compose Hom f h))).

Definition undefined {A : Type} : A. Admitted.

Program Fixpoint denote `(f : Hom a b) : a ~> b :=
  match f in Fix _ x y return x = a -> y = b -> _ with
  | mkFix x y _ _ t => fun _ _ =>
    match t with
    | Inl t =>
      match t with Morph _ f => f end
    | Inr (Inl t) =>
      match t with
      | Id _ => id
      | Compose _ f g => denote f ∘ denote g
      end
    | Inr (Inr t) => undefined
    end
  end eq_refl eq_refl.

Require Import Category.Instance.Coq.

Definition plus' : Hom (nat * nat) nat :=
  composed (morph (prod_curry plus))
           (morph (prod_curry plus)).

Compute plus'.
Compute denote plus'.

Inductive Obj : Type :=
  | One_    : Obj
  | Prod_   : Obj -> Obj -> Obj
  | Exp_    : Obj -> Obj -> Obj
  | Zero_   : Obj
  | Coprod_ : Obj -> Obj -> Obj.

Fixpoint denote `(o : Obj) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_        => 1
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => 0
  | Coprod_ x y => denote x + denote y
  end.
