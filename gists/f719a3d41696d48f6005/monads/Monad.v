Require Export Applicative.

Require Import Ssreflect.ssrfun.

Class Monad (M : Type -> Type) :=
{ is_applicative :> Applicative M

; join : forall {X}, M (M X) -> M X

; monad_law_1 : forall {X},
    (@join X) \o fmap join =1 (@join X) \o (@join _)
; monad_law_2 : forall {X},
    join \o @fmap _ _ _ _ (@pure M is_applicative X) =1 id
; monad_law_3 : forall {X},
    (@join X) \o (@pure _ _ _) =1 id
; monad_law_4 : forall {X Y} (f : X -> Y),
    join \o fmap (fmap f) =1 fmap f \o (@join _)
}.

Notation "join/ M" := (@join M _ _) (at level 28).
Notation "join/ M N" := (@join (fun X => M (N X)) _ _) (at level 26).

Definition bind {M} `{Monad M} {X Y} (f : (X -> M Y)) (x : M X) : M Y :=
  @join M _ Y (@fmap _ _ _ _ f x).

Notation "m >>= f" := (bind f m) (at level 25, left associativity).

Notation "X <-- A ;; B" := (A >>= (fun X => B))
  (right associativity, at level 84, A at next level).

Notation "A ;; B" := (_ <-- A ;; B)
  (right associativity, at level 84, A1 at next level).

Theorem monad_law_1_x
  : forall M (m_dict : Monad M) A (x : M (M (M A))),
  join (fmap join x) = (@join M m_dict A) (join x).
Proof.
  intros.
  assert (join (fmap join x) = (join \o fmap join) x).
    unfold funcomp. reflexivity.
  assert (join (join x) = (join \o join) x).
    unfold funcomp. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_1.
  reflexivity.
Qed.

Theorem monad_law_2_x
  : forall M (m_dict : Monad M) A (x : M A),
  join (@fmap _ _ _ _ (@pure M _ A) x) = x.
Proof.
  intros.
  assert (join (fmap pure x) = (join \o fmap pure) x).
    unfold funcomp. reflexivity.
  rewrite H.
  rewrite monad_law_2.
  reflexivity.
Qed.

Theorem monad_law_3_x
  : forall M (m_dict : Monad M) A (x : M A),
  (@join M m_dict A) (pure x) = x.
Proof.
  intros.
  assert (join (pure x) = (join \o pure) x).
    unfold funcomp. reflexivity.
  rewrite H.
  rewrite monad_law_3.
  reflexivity.
Qed.

Theorem monad_law_4_x
  : forall M (m_dict : Monad M)
      A B (f : A -> B) (x : M (M A)),
  join (fmap (fmap f) x) = fmap f (join x).
Proof.
  intros.
  assert (join (fmap (fmap f) x) = (join \o fmap (fmap f)) x).
    unfold funcomp. reflexivity.
  assert (fmap f (join x) = (fmap f \o join) x).
    unfold funcomp. reflexivity.
  rewrite H. rewrite H0.
  rewrite monad_law_4.
  reflexivity.
Qed.

Theorem monad_assoc : forall M `{Monad M}
  {A B C} (m : M A) (f : A -> M B) (g : B -> M C),
  m >>= f >>= g = m >>= (fun x => f x >>= g).
Proof.
  intros.
  unfold bind.
  rewrite <- monad_law_4_x.
  rewrite fun_composition_x.
  rewrite <- monad_law_1_x.
  rewrite fun_composition_x.
  f_equal.
Qed.

Fixpoint mapM {M} `{Monad M} {A B} (f : A -> M B) (l : list A) : M (list B) :=
  match l with
  | nil => pure nil
  | cons x xs => liftA2 M (@cons _) (f x) (mapM f xs)
  end.

Definition forM {M} `{Monad M} {A B} (l : list A) (f : A -> M B) :
  M (list B) := mapM f l.

Definition foldM {M} `{Monad M} {A B}
  (f : A -> B -> M A) (s : A) (l : list B) : M A :=
  let fix go xs z :=
      match xs with
        | nil => pure z
        | cons y ys => f z y >>= go ys
      end in
  go l s.

Definition forFoldM {M} `{Monad M} {A B}
  (s : A) (l : list B) (f : A -> B -> M A) : M A := foldM f s l.

Fixpoint concat {A} (l : list (list A)) : list A :=
  match l with
  | nil => nil
  | cons x xs => app x (concat xs)
  end.

Definition concatMapM {M} `{Monad M} {A B}
  (f : A -> M (list B)) (l : list A) : M (list B) :=
  concat <$> mapM f l.

Definition mapMaybeM {M} `{Monad M} {A B}
  (f : A -> M (option B)) : list A -> M (list B) :=
  foldM (fun acc x =>
           mx' <-- f x ;;
           pure (match mx' with
             | None => acc
             | Some x' => cons x' acc
             end)) nil.

Definition StateLike (s : Type) (m : Type -> Type) (a : Type) : Type :=
  s -> (s * m a).

Axiom funext : forall a b (f g : a -> b), f =1 g -> f = g.

Program Instance StateLike_Functor {m s} `{Functor m} :
  Functor (StateLike s m) := {
  fmap := fun _ _ f x st =>
    match x st with (st', m) => (st', fmap f m) end
}.
Obligation 1.
  move=> m s functor X x.
  apply funext.
  move=> st.
  simpl.
  case: (x st) => a b.
  by rewrite fun_identity.
Qed.
Obligation 2.
  move=> m s functor X Y Z f g x.
  simpl.
  apply funext.
  move=> st.
  simpl.
  case: (x st) => a b.
  by rewrite fun_composition_x.
Qed.

Program Instance StateLike_Applicative {m s} `{Applicative m} :
  Applicative (StateLike s m) := {
  pure := fun _ x st => (st, pure x);
  ap := fun _ _ f x st =>
          let: (st', f') := f st in
          let: (st'', x') := x st' in
          (st'', ap f' x')
}.
Obligation 1. Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.

Program Instance StateLike_Monad {m s} `{Monad m} :
  Monad (StateLike s m) := {
  join := fun _ x st =>
          let: (st', x') := x st in
          let x'' := x' >>= fun y =>
            let: (st'', y') := y st' in
            y' in
          (st, x'')
}.