Class Monoid (a : Type) := {
  mempty : a;
  mappend : a -> a -> a;

  mempty_left : forall x, mappend mempty x = x;
  mempty_right : forall x, mappend x mempty = x;
  mappend_assoc : forall x y z,
    mappend x (mappend y z) = mappend (mappend x y) z
}.

Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None;
  mappend := fun x y =>
    match x, y with
    | None, x => x
    | x, None => x
    | Some x, Some y => Some (mappend x y)
    end
}.
Next Obligation. destruct x; auto. Qed.
Next Obligation.
  destruct x, y, z; auto.
  now rewrite mappend_assoc.
Qed.

Class Functor (f : Type -> Type) := {
  fmap {a b} : (a -> b) -> f a -> f b;

  fmap_id : forall x, fmap id = @id (f x);
  fmap_comp : forall x y z (f : y -> z) (g : x -> y),
    fmap (f ∘ g) = fmap f ∘ fmap g
}.

Class Applicative (f : Type -> Type) := {
  is_functor :> Functor f;

  pure {a} : a -> f a;
  liftA2 {a b c} : (a -> b -> c) -> f a -> f b -> f c
}.

Program Instance Functor_arrow {x} : Functor (fun y => x -> y) := {
  fmap := fun _ _ => compose
}.

Program Instance Applicative_arrow {x} : Applicative (fun y => x -> y) := {
  pure := fun _ x _ => x;
  liftA2 := fun _ _ _ f x y v => f (x v) (y v);
}.

Program Instance Functor_option : Functor option := {
  fmap := fun _ _ f x =>
    match x with
    | None => None
    | Some x => Some (f x)
    end
}.
Next Obligation.
  extensionality y.
  destruct y; auto.
Qed.
Next Obligation.
  extensionality w.
  destruct w; auto.
Qed.

Program Instance Applicative_option : Applicative option := {
  pure := fun _ x => Some x;
  liftA2 := fun _ _ _ f x y =>
    match x, y with
    | None, _ => None
    | _, None => None
    | Some x, Some y => Some (f x y)
    end
}.

Program Instance Functor_Formula {a} : Functor (Formula a) := {
  fmap := fun _ _ f x v => fmap f (x v)
}.
Next Obligation.
  extensionality y.
  extensionality z.
  unfold id.
  destruct (y z); auto.
Qed.
Next Obligation.
  extensionality w.
  extensionality v.
  unfold compose.
  destruct (w v); auto.
Qed.

Program Instance Applicative_Formula {a : Type} : Applicative (Formula a) := {
  pure := fun _ x _ => Some x
}.
Next Obligation.
Admitted.
