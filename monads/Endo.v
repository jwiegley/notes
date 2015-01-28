Require Import Ssreflect.ssrfun.

Generalizable All Variables.

(* Even though we have the Category class in Category.v, the Functors
   and Monads I'm interested in reasoning about are all endofunctors on
   Coq, so there is no reason to carry around that extra machinery. *)

Class Functor (F : Type -> Type) :=
{ fobj := F
; fmap : forall {X Y}, (X -> Y) -> F X -> F Y

; fun_identity : forall {X}, @fmap _ _ (@id X) =1 id
; fun_composition : forall {X Y Z} (f : Y -> Z) (g : X -> Y),
    fmap f \o fmap g =1 @fmap _ _ (f \o g)
}.

Arguments fmap            [F] [Functor] [X] [Y] f g.
Arguments fun_identity    [F] [Functor] [X] x.
Arguments fun_composition [F] [Functor] [X] [Y] [Z] f g x.

Notation "f <$> g" := (fmap f g) (at level 28, left associativity).

Notation "fmap[ M ]  f" := (@fmap M _ f) (at level 28).
Notation "fmap[ M N ]  f" := (@fmap (fun X => M (N X)) _ f) (at level 26).
Notation "fmap[ M N O ]  f" := (@fmap (fun X => M (N (O X))) _ f) (at level 24).

Coercion fobj : Functor >-> Funclass.

Section Functors.

  Variable F : Type -> Type.
  Context `{Functor F}.

  Theorem fun_composition_x
    : forall {X Y Z} (f : Y -> Z) (g : X -> Y) (x : F X),
    f <$> (g <$> x) = (f \o g) <$> x.
  Proof.
    intros.
    rewrite <- fun_composition.
    reflexivity.
  Qed.

End Functors.
