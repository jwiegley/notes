Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Functor.Representable.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(** Model *)

Definition mstream
           `(f : C ⟶ Sets) `{@Representable _ f}
           (m : C ⟶ C) (a : C) := f (m a).

(*
Definition pipe (a' a b' b : Type)  (m : Type -> Type) (r : Type) :=
  mstream (ReaderT a' (EitherT r m)) a ~>
  mstream (ReaderT b' (EitherT r m)) b.
*)

(** Representation *)

Inductive Proxy (a' a b' b : Type) (m : Type -> Type) (r : Type) :=
  | Request (_ : a') (_ : a  -> Proxy a' a b' b m r)
  | Respond (_ : b)  (_ : b' -> Proxy a' a b' b m r)
  | M x     (_ : x -> Proxy a' a b' b m r) (_ : m x)
  | Pure    (_ : r).

Arguments Request {a' a b' b m r} _ _.
Arguments Respond {a' a b' b m r} _ _.
Arguments M       {a' a b' b m r x} _ _.
Arguments Pure    {a' a b' b m r} _.

(** Denotation *)

(*
Fixpoint denote {a' a b' b : Type} `{Monad m} {r : Type}
         (p : Proxy a' a b' b m r) : pipe a' a b' b m r :=
  fun f n b' =>
    match p with
    | Request a' ka  =>
      a <- f n a' ;
      denote (ka a) f (S n) b'
    | Respond b  kb' =>
      denote (kb' b') f (S n) b'
    | M k m =>
      p' <- inr <$> m ;
      denote (k p') f (S n) b'
    | Pure x => pure (inl x)
    end.

Notation "〚 x 〛" := (denote x).
*)
