Require Export Endo.

Require Import Ssreflect.ssrfun.

Generalizable All Variables.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (F : Type -> Type) :=
{ is_functor :> Functor F

; pure : forall {X}, X -> F X
; ap : forall {X Y}, F (X -> Y) -> F X -> F Y
    where "f <*> g" := (ap f g)

; app_identity : forall {X}, @ap _ _ (@pure _ (@id X)) =1 id
; app_composition
    : forall {X Y Z} (u : F (Y -> Z)) (v : F (X -> Y)) (w : F X),
    pure comp <*> u <*> v <*> w = u <*> (v <*> w)
; app_homomorphism : forall {X Y} (x : X) (f : X -> Y),
    pure f <*> pure x = @pure _ (f x)
; app_interchange : forall {X Y} (y : X) (u : F (X -> Y)),
    u <*> pure y = pure (fun f => f y) <*> u

; app_imap_unit : forall {X Y} (f : X -> Y),
    ap (pure f) = @fmap _ _ _ _ f
}.

Notation "pure/ M" := (@pure M _) (at level 28).
Notation "pure/ M N" := (@pure (fun X => M (N X)) _) (at level 26).

Notation "ap[ M ]  f" := (@ap M _ _ f) (at level 28).
Notation "ap[ M N ]  f" := (@ap (fun X => M (N X)) _ _ f) (at level 26).
Notation "ap[ M N O ]  f" := (@ap (fun X => M (N (O X))) _ _ f) (at level 24).

Notation "f <*> g" := (ap f g) (at level 28, left associativity).

Notation "[| f x y .. z |]" := (.. (f <$> x <*> y) .. <*> z)
    (at level 9, left associativity, f at level 9,
     x at level 9, y at level 9, z at level 9).

Definition app_merge {X Y Z W} (f : X -> Y) (g : Z -> W)
  (t : X * Z) : Y * W  :=
  match t with (x, z) => (f x, g z) end.

Definition app_prod {F} `{Applicative F}
  {X Y} (x : F X) (y : F Y) : F (X * Y)%type := pair <$> x <*> y.

Notation "f *** g" := (app_merge f g) (at level 28, left associativity).

Notation "f ** g" := (app_prod f g) (at level 28, left associativity).

Ltac rewrite_app_homomorphisms :=
  (repeat (rewrite <- app_imap_unit);
   rewrite app_homomorphism;
   repeat (rewrite app_imap_unit)).

Section Applicatives.

  Variable F : Type -> Type.
  Context `{Applicative F}.

  Theorem app_homomorphism_2
    : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
    f <$> pure x <*> pure y = @pure _ _ _ (f x y).
  Proof.
    intros.
    rewrite <- app_homomorphism.
    rewrite <- app_homomorphism.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  (* This theorem was given as an exercise by Brent Yorgey at:

     http://www.haskell.org/haskellwiki/Typeclassopedia#Applicative
  *)
  Theorem app_flip : forall {X Y} (x : F X) (f : X -> Y),
    pure f <*> x = pure (fun x f => f x) <*> x <*> pure f.
  Proof.
    intros.
    rewrite app_interchange.
    rewrite <- app_composition.
    rewrite app_imap_unit.
    rewrite app_imap_unit.
    rewrite app_homomorphism_2.
    unfold funcomp.
    rewrite app_imap_unit.
    reflexivity.
  Qed.

  Definition app_unit : F unit := pure tt.

  Theorem app_embed
    : forall {G : Type -> Type} `{Applicative G}
             {X Y} (x : G (X -> Y)) (y : G X),
    pure (x <*> y) = pure ap <*> pure x <*> @pure _ _ _ y.
  Proof.
    intros.
    rewrite_app_homomorphisms.
    rewrite <- app_homomorphism.
    rewrite <- app_imap_unit.
    reflexivity.
  Qed.

  Theorem app_naturality
    : forall {A B C D}
             (f : A -> C) (g : B -> D) (u : F A) (v : F B),
    fmap (f *** g) (u ** v) = (fmap f u) ** (fmap g v).
  Proof.
    intros.
    unfold app_prod.
    rewrite <- app_imap_unit.
    rewrite fun_composition_x.
    repeat (rewrite <- app_imap_unit).
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite <- app_composition.
    rewrite app_composition.
    rewrite app_composition.
    f_equal.
    rewrite_app_homomorphisms.
    rewrite fun_composition_x.
    rewrite fun_composition_x.
    rewrite app_interchange.
    rewrite app_imap_unit.
    rewrite fun_composition_x.
    f_equal.
  Qed.

  Definition liftA2 {A B C} (f : A -> B -> C)
    (x : F A) (y : F B) : F C :=
    f <$> x <*> y.

End Applicatives.
