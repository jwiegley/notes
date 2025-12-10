Require Import
  Coq.Program.Program
  Hask.Control.Monad
  Hask.Control.Monad.Trans.Either
  Hask.Control.Monad.Trans.Reader.

Generalizable All Variables.

(** Model *)

Definition mstream (m : Type -> Type) (a : Type) := nat -> m a.

Definition pipe (a' a b' b : Type)  (m : Type -> Type) (r : Type) :=
  mstream (ReaderT a' (EitherT r m)) a ->
  mstream (ReaderT b' (EitherT r m)) b.

(** Representation *)

CoInductive Proxy (a' a b' b : Type) (m : Type -> Type) (r : Type) :=
  | Request (_ : a') (_ : a  -> Proxy a' a b' b m r)
  | Respond (_ : b)  (_ : b' -> Proxy a' a b' b m r)
  | M x     (_ : x -> Proxy a' a b' b m r) (_ : m x)
  | Pure    (_ : r).

Arguments Request {a' a b' b m r} _ _.
Arguments Respond {a' a b' b m r} _ _.
Arguments M       {a' a b' b m r x} _ _.
Arguments Pure    {a' a b' b m r} _.

(** Denotation *)

Fixpoint denote {a' a b' b : Type} `{Monad m} {r : Type}
         (p : Proxy a' a b' b m r)
         (f : mstream (ReaderT a' (EitherT r m)) a) (n : nat) (x : b') :
  EitherT r m b :=
  match n with
  | O => _
  | S x => _
  end
  match p with
  | Request a' ka  =>
    a <- f n a' ;
    denote (ka a) f (S n) x
  | Respond b  kb' =>
    denote (kb' x) f (S n) x
  | M k m =>
    p' <- fmap inr m ;
    denote (k p') f (S n) x
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

Program Definition pipe_id {a' a m r} : pipe a' a a' a m r :=
  fun k n b' => k n b'.

Program Instance Pipes_Category (m : Type -> Type) (r : Type) :
  Category (Type * Type) (fun '(a', a) '(b', b) => pipe a' a b' b m r)  := {
  id := fun '(a', a) => @pipe_id a' a m r;
  compose := fun _ _ _ f g => _
}.
Next Obligation.
  unfold pipe in *.
  intuition.
Defined.

Program Definition Proxy_id {a' a m r} (n : nat) (default : r) :
  a' -> Proxy a' a a' a m r :=
  let fix go n :=
      match n with
      | O => fun _ => Pure default
      | S n' => fun a' => Request a' (fun a => Respond a (go n'))
      end in go n.

Lemma denote_id {a' a m} `{Monad m} {r} (n : nat) (default : r) (x : a') :
  〚 Proxy_id n default x 〛= @id _ _ (Pipes_Category m r) (a', a).
Proof.
  induction n; simpl.
    admit.
  extensionality k.
  extensionality n'.
  extensionality z.
  unfold EitherT_join.
  unfold EitherT_map.
Abort.
