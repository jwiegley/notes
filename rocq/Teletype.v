Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Free.
Require Import Hask.Control.Monad.Free.
Require Import Coq.Strings.String.

Open Scope string_scope.

Generalizable All Variables.

Inductive TeletypeF a b r :=
  | Get : (a -> r) -> TeletypeF a b r
  | GetMany : ((forall s : Type, s -> (a -> s -> s) -> s) -> r) -> TeletypeF a b r
  | Put : b -> r -> TeletypeF a b r.

Arguments Get {a b r} k.
Arguments GetMany {a b r} k.
Arguments Put {a b r} x z.

Program Instance TeletypeF_Functor {a b} : Functor (@TeletypeF a b) := {
  fmap := fun _ _ f x => match x with
    | Get k     => Get (f \o k)
    | GetMany k => GetMany (f \o k)
    | Put b r   => Put b (f r)
    end
}.

Definition Teletype a b := Free (TeletypeF a b).

Definition foo (f : nat -> string) (g : list nat -> string) :
  Teletype nat string unit :=
  a <- liftF (Get id);
  b <- liftF (GetMany (fun k => k _ nil (@cons _)));
  liftF (Put (f a) tt) ;;
  liftF (Put (g b) tt).

Definition TeletypeT a b := FreeT (TeletypeF a b).

Require Import Hask.Control.Monad.Trans.Free.

Definition bar (f : nat -> string) (g : list nat -> string) `{Monad m} :
  TeletypeT nat string m unit :=
  a <- liftF (Get id);
  b <- liftF (GetMany (fun k =>
          k (m (list nat)) (return_ nil)
            (fun (a : nat) rest => cons a <$> rest)));
  b' <- liftFM b;
  liftF (Put (f a) tt) ;;
  liftF (Put (g b') tt).

Definition phi `{Monad m} `(x : TeletypeF nat string (m r)) : m r :=
  match x with
  | Get k     => k 0
  | GetMany k => k (fun _ z f =>
                      x <- f 0 z;
                      f 1 x)
  | Put b r   => r
  end.

Definition eval {r} := iter (phi (r:=r)).
Definition evalT {r} := iterT (phi (r:=r)).
