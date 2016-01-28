Require Import Coq.Program.Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Set Boolean Equality Schemes.
Set Decidable Equality Schemes.

Inductive Ident (a : Type) := Id : a -> Ident a.

(*****************************************************************************)

Infix "\o" := compose (at level 50).

Class Functor (f : Type -> Type) : Type := {
  fmap : forall {a b : Type}, (a -> b) -> f a -> f b;
  fmap_id   : forall a : Type, fmap (@id a) = id;
  fmap_comp : forall (a b c : Type) (f : b -> c) (g : a -> b),
    fmap f \o fmap g = fmap (f \o g)
}.

Arguments fmap {f _ a b} g x.

Corollary fmap_comp_x `{Functor F} :
  forall (a b c : Type) (f : b -> c) (g : a -> b) x,
  fmap f (fmap g x) = fmap (fun y => f (g y)) x.
Proof.
  intros.
  pose proof (fmap_comp f g) as H0.
  unfold compose in H0.
  rewrite <- H0.
  reflexivity.
Qed.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure : forall a : Type, a -> f a;
  ap   : forall a b : Type, f (a -> b) -> f a -> f b
    where "f <*> g" := (ap f g);

  ap_id : forall a : Type, ap (pure (@id a)) = id;
  ap_comp : forall (a b c : Type) (v : f (a -> b)) (u : f (b -> c)) (w : f a),
    pure (fun f g x => f (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : forall (a b : Type) (x : a) (f : a -> b),
    pure f <*> pure x = pure (f x);
  ap_interchange : forall (a b : Type) (y : a) (u : f (a -> b)),
    u <*> pure y = pure (fun f => f y) <*> u;

  ap_fmap : forall (a b : Type) (f : a -> b),
    ap (pure f) = @fmap _ is_functor _ _ f
}.

Arguments pure {f _ _} _.
Arguments ap   {f _ _ _} _ x.

Infix "<*>" := ap (at level 28, left associativity).

Definition liftA2 `{Applicative m} {A B C : Type}
  (f : A -> B -> C) (x : m A) (y : m B) : m C := ap (fmap f x) y.

Reserved Notation "f <|> g" (at level 28, left associativity).

Class Alternative (F : Type -> Type) `{Applicative F} :=
{ zero : forall {X}, F X
; choose : forall {X}, F X -> F X -> F X
    where "f <|> g" := (choose f g)
}.

Notation "f <|> g" := (choose f g) (at level 28, left associativity).

Class Monad (m : Type -> Type) := {
  is_applicative :> Applicative m;

  join : forall {a : Type}, m (m a) -> m a;

  join_fmap_join : forall a, join \o fmap (@join a) = join \o join;
  join_fmap_pure : forall a, join \o fmap (pure (a:=a)) = id;
  join_pure      : forall a, join \o pure (a:=m a) = @id (m a);
  join_fmap_fmap : forall a b (f : a -> b),
    join \o fmap (fmap f) = fmap f \o join
}.

(*****************************************************************************)

Definition Free effect (a : Type) := forall `{Monad m}, effect m -> m a.

(*****************************************************************************)

Require Import FunctionalExtensionality.

Ltac lawful :=
  try unfold compose;
  intros;
  repeat match goal with
    [ |- ?X = ?Y ] =>
      (apply (@functional_extensionality _ _ X Y) ||
       apply (@functional_extensionality_dep _ _ X Y)) ; intros
  end;
  match goal with
    [ H : Monad ?M |- _ ] =>
      pose proof (@is_applicative M H) as HA;
      pose proof (@is_functor M HA) as HF
  end;
  try first [ rewrite fmap_id
            | rewrite fmap_comp_x
            | rewrite ap_id
            | rewrite ap_comp
            | rewrite ap_homo
            | rewrite ap_interchange
            | rewrite ap_fmap
            | rewrite join_fmap_join
            | rewrite join_fmap_pure
            | rewrite join_pure
            | rewrite join_fmap_fmap ];
  auto.

Obligation Tactic := lawful.

Program Instance Free_Functor : Functor (Free effect) := {
  fmap := fun _ _ f x => fun m H e => fmap f (x m H e)
}.

Program Instance Free_Applicative : Applicative (Free effect) := {
  pure := fun _ x => fun _ _ _ => pure x;
  ap   := fun _ _ mf mx => fun m H e => mf m H e <*> mx m H e
}.

Program Instance Free_Monad : Monad (Free effect) := {
  join := fun _ x => fun m H e =>
            join (fmap (fun m' => m' m H e) (x m H e))
}.

(*****************************************************************************)

Record Effects (m : Type -> Type) := E {
  getCharEff : m nat;
  putCharEff : nat -> m unit;
  forkIOEff : forall a, m a -> m nat
}.

Arguments getCharEff {m} _.

Definition IO := Free Effects.

Definition foo : IO nat := fun m H e => @getCharEff m e.

Arguments foo {m _} _.

(*****************************************************************************)

Require Import Hask.Data.Functor.Identity.

Definition Id_Effects : Effects IdentityF :=
  {| getCharEff := Id _ 10
   ; putCharEff := fun n => Id _ tt
   ; forkIOEff  := fun a (act : IdentityF a) => Id _ 10
   |}.

Compute (foo Id_Effects).
