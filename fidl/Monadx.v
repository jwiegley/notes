Require Export Fiat.ADT.

Close Scope comp_scope.
Open Scope string_scope.
Open Scope bool_scope.

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

Infix "<$>" := fmap (at level 28, left associativity, only parsing).
Notation "x <&> f" :=
  (fmap f x) (at level 28, left associativity, only parsing).

Notation "fmap[ M ]  f" := (@fmap M _ _ _ f) (at level 28).
Notation "fmap[ M N ]  f" := (@fmap (fun X => M (N X)) _ _ _ f) (at level 26).
Notation "fmap[ M N O ]  f" :=
  (@fmap (fun X => M (N (O X))) _ _ _ f) (at level 24).

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

Notation "pure[ M ]  x" := (@pure M _ _ x) (at level 28).
Notation "pure[ M N ]  x" := (@pure (fun X => M (N X)) _ _ x) (at level 26).
Notation "pure[ M N O ]  x" :=
  (@pure (fun X => M (N (O X))) _ _ x) (at level 24).

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

Arguments join {m _ _} _.

Notation "join[ M ]  x" := (@join M _ _ x) (at level 28).
Notation "join[ M N ]  x" := (@join (fun X => M (N X)) _ _ x) (at level 26).
Notation "join[ M N O ]  x" :=
  (@join (fun X => M (N (O X))) _ _ x) (at level 24).

Corollary join_fmap_join_x `{Monad m} : forall a x,
  join (fmap (join (a:=a)) x) = join (join x).
Proof.
Admitted.

Corollary join_fmap_pure_x `{Monad m} : forall a x,
  join (fmap (pure (a:=a)) x) = x.
Proof.
Admitted.

Corollary join_pure_x `{Monad m} : forall a x,
  join (pure (a:=m a) x) = x.
Proof.
  intros.
  pose proof (join_pure a).
  unfold compose in H0.
  replace x with (id x) at 2.
    rewrite <- H0.
    reflexivity.
  reflexivity.
Qed.

Corollary join_fmap_fmap_x `{Monad m} : forall (a b : Type) (f : a -> b) x,
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
Admitted.

Definition bind `{Monad m} {X Y : Type} (f : (X -> m Y)) : m X -> m Y :=
  join \o fmap f.

Delimit Scope monad_scope with monad.

Notation "m >>= f" :=
  (bind f m) (at level 42, right associativity) : monad_scope.
Notation "f =<< m" :=
  (bind f m) (at level 42, right associativity) : monad_scope.
Notation "a >> b" :=
  (a >>= fun _ => b)%monad (at level 81, right associativity) : monad_scope.

Definition kleisli_compose `{Monad m} `(f : a -> m b) `(g : b -> m c) :
  a -> m c := fun x => (f x >>= g)%monad.

Infix ">=>" := kleisli_compose (at level 42, right associativity) : monad_scope.
Notation "f <=< g" :=
  (kleisli_compose g f) (at level 42, right associativity) : monad_scope.

Notation "f >=[ m ]=> g" :=
  (@kleisli_compose _ m _ _ f _ g)
    (at level 42, right associativity) : monad_scope.
Notation "f <=[ m ]=< g" :=
  (@kleisli_compose _ m _ _ g _ f)
    (at level 42, right associativity) : monad_scope.

Notation "X <- A ; B" := (A >>= (fun X => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "'prj' ( X , Y ) <- A ; B" :=
  (A >>= (fun p => match p with (X, Y) => B end))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Notation "A ;; B" := (A >>= (fun _ => B))%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Open Scope monad_scope.

Definition when `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if b then x else pure tt.

Definition unless `{Monad m} `(b : bool) (x : m unit) : m unit :=
  if negb b then x else pure tt.

Fixpoint mapM `{Applicative m} {A B} (f : A -> m B) (l : list A) :
  m (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 (@cons _) (f x) (mapM f xs)
  end.

Definition forM `{Applicative m} {A B} (l : list A) (f : A -> m B) :
  m (list B) := mapM f l.

Fixpoint mapM_ `{Monad m} {A B} (f : A -> m B) (l : list A) : m unit :=
  match l with
  | nil => pure tt
  | cons x xs => f x >> mapM_ f xs
  end.

Definition forM_ `{Monad m} {A B} (l : list A) (f : A -> m B) : m unit :=
  mapM_ f l.

Definition foldM `{Monad m} {A : Type} {B : Type}
  (f : A -> B -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition foldrM `{Monad m} {A : Type} {B : Type}
  (f : B -> A -> m A) (s : A) (l : list B) : m A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => go ys z >>= f y
      end in
  go l s.
