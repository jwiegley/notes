Inductive Yoneda (f : Type -> Type) (a : Type) : Type :=
  | Y : forall {b : Type}, ((a -> b) -> f b) -> Yoneda f a.

Theorem is_iso : forall {X : Type} {Y : Type} (x : X) (y : Y) (to : X -> Y) (from : Y -> X),
  from (to x) = x.
Proof.
  intros.

Definition id {X : Type} (a : X) : X := a.

Definition fmap {f : Type -> Type} {X Y : Type} (k : X -> Y) : (f X -> f Y) :=
  admit.

Definition lift_yoneda {f : Type -> Type} {X : Type} (a : f X) : Yoneda f X :=
  Y (fun k => fmap k a).

Definition lower_yoneda (f : Type -> Type) (X : Type) (a : Yoneda f X) : f X :=
  admit.

Theorem yoneda_lemma : forall (f : Type -> Type) (a : Type),
  is_iso (f a) (Yoneda f a) (lift_yoneda f a) (lower_yoneda f a).
Proof.
  intros. 
