Inductive Yoneda (F : Type -> Type) (X : Type) : Type :=
  | Embed : (forall {Y}, (X -> Y) -> F Y) -> Yoneda F X.

Definition is_iso (X Y : Type) (x : X) (y : Y)
  (to : X -> Y) (from : Y -> X) : Prop := from (to x) = x.

Definition id {X : Type} (a : X) : X := a.

Definition compose {A B C : Type}
  (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 60, right associativity).

Class Functor (F : Type -> Type) := {
  fmap : forall {X Y}, (X -> Y) -> F X -> F Y;
  functor_law_1 : forall {X} (x : F X), fmap (@id X) x = @id (F X) x;
  functor_law_2 : forall {X Y Z} (x : F X) (f : Y -> Z) (g : X -> Y),
   (fmap f ∘ fmap g) x = fmap (f ∘ g) x
}.

Global Instance List_Functor : Functor list := {
  fmap X Y := map
}.
Proof.
  (* functor_law_1 *)
  intros. induction x as [| x'].
  Case "x = nil". reflexivity.
  Case "x = cons". simpl. rewrite IHx. reflexivity.

  (* functor_law_2 *)
  intros. induction x as [| x'].
  Case "x = nil". reflexivity.
  Case "x = cons".
    unfold compose. unfold compose in IHx.
    simpl. rewrite IHx. reflexivity.  Qed.

Definition lift_yoneda (F : Type -> Type) (f_dict : Functor F)
  (X : Type) (a : F X) : Yoneda F X := Embed F X (fun _ f => fmap f a).

Definition lower_yoneda (F : Type -> Type) (X : Type) (a : Yoneda F X) : F X :=
  match a with | Embed x => x X id end.

Theorem yoneda_lemma : forall (F : Type -> Type) (f_dict : Functor F)
  (X : Type) (o : F X) (p : Yoneda F X),
    is_iso (F X) (Yoneda F X) o p
      (lift_yoneda F f_dict X) (lower_yoneda F X).
Proof.
  intros. unfold is_iso. unfold lift_yoneda. unfold lower_yoneda.
  apply functor_law_1.  Qed.
