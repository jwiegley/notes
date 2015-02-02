Require Import Function.
Require Import Functor.

Class Applicative (F: Type -> Type) := {
    (* It must also be a functor *)
    is_functor :> Functor F;

    (* functions *)
    unit : forall {A : Type}, A -> F A;
    apply : forall {A B : Type}, F (A -> B) -> F A -> F B;


    (* laws *)
    unit_identity
        : forall (A : Type) (x : F A), apply (unit id) x = x;

    unit_compose
        : forall (A B C : Type) (u : F (B -> C)) (v : F (A -> B)) (w : F A)
        , apply (apply (apply (unit compose) u) v) w = apply u (apply v w);

    unit_homomorphism
        : forall (A B : Type) (f : A -> B) (x : A)
        , apply (unit f) (unit x) = unit (f x);

    unit_interchange
        : forall (A B : Type) (u : F (A -> B)) (x : A)
        , apply u (unit x) = apply (unit (fun (f : A -> B) => f x)) u;

    unit_fmap
        : forall (A B : Type) (f : A -> B) (x : F A)
        , fmap f x = apply (unit f) x
}.

Notation "v <*> w" := (apply v w) (at level 50).

Theorem fmap_unit
    : forall (F : Type -> Type) (app_dict : Applicative F) (A B : Type) (f : A -> B) (x : A)
    , fmap f (unit x) = unit (f x).
Proof.
    intros.
    rewrite -> unit_fmap.
    rewrite -> unit_interchange.
    rewrite -> unit_homomorphism.
    reflexivity.
Qed.
