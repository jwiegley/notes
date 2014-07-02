Inductive Yoneda (f : Type -> Type) (a : Type) : Type :=
  | Y : (forall (b : Type), (a -> b) -> f b) -> Yoneda f a.

Definition is_iso (X Y : Type) (x : X) (y : Y) (to : X -> Y) (from : Y -> X) : Prop :=
  from (to x) = x.

Definition id {X : Type} (a : X) : X := a.

Fixpoint fmap (X Y : Type) (k : X -> Y) (xs : list X) : list Y :=
  match xs with
    | nil => nil
    | cons x x0 => k x :: fmap X Y k x0
  end.

Theorem fst_functor_law : forall (X : Type) (x : list X),
  fmap X X id x = x.
Proof.
  intros. induction x as [| x'].
  Case "x = nil".
  reflexivity.
  Case "x = cons".
  simpl. rewrite IHx. reflexivity.  Qed.

Definition lift_yoneda (X : Type) (a : list X) : Yoneda list X :=
  Y list X (fun b k => fmap X b k a).

Definition lower_yoneda (f : Type -> Type) (X : Type) (a : Yoneda f X) : f X :=
  match a with
    | Y x => x X id
  end.

Theorem yoneda_lemma : forall (a : Type) (o : list a) (p : Yoneda list a),
  is_iso (list a) (Yoneda list a) o p (lift_yoneda a) (lower_yoneda list a).
Proof.
  intros. unfold is_iso. unfold lift_yoneda. unfold lower_yoneda.
  apply fst_functor_law.  Qed.
