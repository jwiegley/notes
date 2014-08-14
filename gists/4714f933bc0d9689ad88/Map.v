Axiom ext_eq : forall {T1 T2 : Type} (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Type) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
Proof.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.

Definition id {X} (a : X) : X := a.

Definition compose {A B C} (f : B -> C) (g : A -> B) (x : A) : C := f (g x).

Notation "f ∘ g" := (compose f g) (at level 69, right associativity).

Fixpoint map {A B : Set} (f : A -> B) (xs : list A) : list B :=
  match xs with
  | nil => nil
  | cons y ys => cons (f y) (map f ys)
  end.

Theorem map_composition : forall {A B C : Set} (f : A -> B) (g : B -> C),
  map (@id A) = id -> map g ∘ map f = map (g ∘ f).
Proof.
  intros. ext_eq.
  unfold compose.
  induction x; simpl.
    reflexivity.
  f_equal. rewrite IHx.
  reflexivity.
Qed.