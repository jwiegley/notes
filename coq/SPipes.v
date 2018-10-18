Require Import
  Coq.Program.Program
  Hask.Control.Monad
  Hask.Control.Monad.Trans.Either
  Hask.Control.Monad.Trans.Reader.

Generalizable All Variables.

(** Model *)

Definition mstream (m : Type -> Type) (a : Type) := nat -> m a.

Definition pipe (a b : Type)  (m : Type -> Type) (r : Type) :=
  mstream (EitherT r m) a -> mstream (EitherT r m) b.

(** Representation *)

Inductive Proxy (a b : Type) (m : Type -> Type) (r : Type) :=
  | Request (_ : a -> Proxy a b m r)
  | Respond (_ : b) (_ : Proxy a b m r)
  | M x     (_ : x -> Proxy a b m r) (_ : m x)
  | Pure    (_ : r).

Arguments Request {a b m r} _.
Arguments Respond {a b m r} _ _.
Arguments M       {a b m r x} _ _.
Arguments Pure    {a b m r} _.

(** Denotation *)

Fixpoint denote {a b : Type} `{Monad m} {r : Type}
         (p : Proxy a b m r)
         (f : mstream (EitherT r m) a) (n : nat) : EitherT r m b :=
  match p with
  | Request ka  =>
    a <- f n ;
    denote (ka a) f n
  | Respond b  k =>
    match n with
    | O => pure (inr b)
    | S n => denote k f n
    end
  | M k m =>
    p' <- fmap inr m ;
    denote (k p') f n
  | Pure x => pure (inl x)
  end.

Notation "〚 x 〛" := (denote x).

(** Algebras *)

Reserved Infix "∘" (at level 40, left associativity).

Class Category (obj : Type) (hom : obj -> obj -> Type) := {
  id {x} : hom x x;
  compose {x y z} (f: hom y z) (g : hom x y) : hom x z
    where "f ∘ g" := (compose f g);

  id_left  {x y} (f : hom x y) : id ∘ f = f;
  id_right {x y} (f : hom x y) : f ∘ id = f;

  comp_assoc {x y z w} (f : hom z w) (g : hom y z) (h : hom x y) :
    f ∘ (g ∘ h) = (f ∘ g) ∘ h;
}.

Program Instance Coq_Category : Category Type arrow := {
  id := @Datatypes.id;
  compose := @comp
}.

Program Definition pipe_id {a m r} : pipe a a m r :=
  fun k n => k n.

Program Instance Pipes_Category (m : Type -> Type) (r : Type) :
  Category Type (fun a b => pipe a b m r)  := {
  id := fun a => @pipe_id a m r;
  compose := fun _ _ _ f g => _
}.
Next Obligation.
  unfold pipe in *.
  intuition.
Defined.

Fixpoint Proxy_id {a m r} (n : nat) (default : r) : Proxy a a m r :=
  match n with
  | O => Pure default
  | S n => Request (fun a => Respond a (Proxy_id n default))
  end.
  
Import MonadLaws.

Lemma denote_id {a m} `{MonadLaws m} {r} f (n : nat) (default : r) :
  n > 0 ->
  〚 Proxy_id n default 〛f n  = @id _ _ (Pipes_Category m r) a f n.
Proof.
  intros.
  induction n; simpl.
    admit.
  unfold EitherT_join.
  unfold EitherT_map.
  simpl.
  unfold Either.Either_map.
  rewrite fmap_comp_x.
  unfold pipe_id.
Abort.
