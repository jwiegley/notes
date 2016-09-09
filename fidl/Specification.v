Inductive eq' : forall (A : Type), A -> A -> Prop :=
  eq_refl' A : forall (x : A), eq' A x x.

Lemma should_be_true : forall A (x y : A), eq' A x y <-> x = y.
Proof.
  split; intros.
    destruct H.
    reflexivity.
  rewrite H.
  constructor.
Qed.

Goal @eq nat 10 20 -> False.
  intros.
  inversion H.
Qed.

Goal @eq' nat 10 20 -> False.
  intros.
  apply should_be_true in H.
  inversion H.
Qed.

Require Export
  Coq.Sets.Ensembles
  Coq.Strings.String
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

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

(****************************************************************************)

Require Import FunctionalExtensionality.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Local Transparent Bind.

Ltac breakdown :=
  try unfold id, compose in *;
  repeat match goal with
  | [ H : ex ?X |- _ ] => destruct H
  | [ |- (fun _ => _) = (fun _ => _) ] =>
      extensionality x; simpl;
      extensionality z; apply prop_ext; split; intros
  | [ |- (exists _, _) = (exists _, _) ] => apply prop_ext
  | [ H : (_ <- _; _)%comp ?Z |- _ ] => destruct H
  | [ H : (_ <- _; _ <- _; _)%comp ?Z |- _ ] => destruct H
  | [ H : (_ <- (_ <- _; _); _)%comp ?Z |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => inversion H; clear H
  | [ |- _ /\ _ ] => split; intros
  | [ H : In _ _ _ |- _ ] => inversion H; clear H
  | [ H : _ = _ |- _ ] => subst
  | [ H : In _ ?X ?Y |- ?X ?Y ] => apply H
  | [ |- _%comp ?Z ] => unfold Bind
  end;
  try eauto;
  try constructor;
  repeat eexists;
  try (eapply (functional_extensionality _); intros);
  try assumption;
  try (apply prop_ext; split; intros; breakdown).

Obligation Tactic :=
  intros; simpl;
  try solve [
    breakdown;
    try match goal with [ H : _%comp ?Z |- _ ] => destruct H end;
    breakdown
  ].

(****************************************************************************)

Inductive Maybe (A : Type) := Nothing | Just : A -> Maybe A.
Arguments Nothing {A}.
Arguments Just {A} _.

Definition Maybe_map `(f : X -> Y) (x : Maybe X) : Maybe Y :=
  match x with
  | Nothing => Nothing
  | Just x' => Just (f x')
  end.

Program Instance Maybe_Functor : Functor Maybe :=
{ fmap := @Maybe_map
}.

Definition Maybe_apply {X Y} (f : Maybe (X -> Y)) (x : Maybe X) : Maybe Y :=
  match f with
  | Nothing => Nothing
  | Just f' => match x with
    | Nothing => Nothing
    | Just x' => Just (f' x')
    end
  end.

Program Instance Maybe_Applicative : Applicative Maybe :=
{ is_functor := Maybe_Functor
; pure := @Just
; ap := @Maybe_apply
}.
Obligation 2. destruct w, v, u; simpl; auto. Qed.

Program Instance Maybe_Alternative : @Alternative Maybe Maybe_Applicative :=
{ zero := @Nothing
; choose := fun _ x y => match x with
                         | Nothing => y
                         | Just _ => x
                         end
}.

Definition Maybe_join {X} (x : Maybe (Maybe X)) : Maybe X :=
  match x with
  | Nothing => Nothing
  | Just Nothing => Nothing
  | Just (Just x') => Just x'
  end.

Program Instance Maybe_Monad : Monad Maybe :=
{ is_applicative := Maybe_Applicative
; join := @Maybe_join
}.
Obligation 1.
  extensionality m.
  do 3 (destruct m; simpl; auto).
Qed.
Obligation 4.
  extensionality m.
  do 3 (destruct m; simpl; auto).
Qed.

(****************************************************************************)

Program Instance Comp_Functor : Functor Comp := {
  fmap := fun A B f (x : Comp A) =>
    (v <- x; ret (f v))%comp
}.

Program Instance Comp_Applicative : Applicative Comp := {
  pure := fun _ x => (ret x)%comp;
  ap   := fun A B mf mx =>
    (f <- mf;
     x <- mx;
     ret (f x))%comp
}.

Program Instance Comp_Monad : Monad Comp := {
  join := fun A m => (m >>= id)%comp
}.
Obligation 1.
  Local Transparent ret.
  unfold id, Bind, ret.
  extensionality x; simpl.
  extensionality z.
  apply prop_ext; split; intros.
    repeat destruct H.
    repeat destruct H1.
    repeat destruct H0.
    exists x0.
    split.
      eexists; split.
        apply H.
      assumption.
    assumption.
  repeat destruct H.
  repeat destruct H1.
  repeat destruct H0.
  eexists.
  split.
    eexists; split.
      apply H.
    constructor.
  eexists; split.
    apply H1.
  assumption.
Qed.

(****************************************************************************)

Class Traversable `{Functor t} := {
  sequence : forall `{Applicative f} a, t (f a) -> f (t a)

  (* naturality
       t . sequence = sequence . fmap t for every applicative transformation t
     identity
       sequence . fmap Identity = Identity
     composition
       sequence . fmap Compose = Compose . fmap sequence . sequence
  *)
}.

Arguments sequence {t H _ f _ a} _.

Arguments Traversable t [H].

(* Tupersable is a specialization of Traversable that applies only to tuples,
   and thus does not require that tuples be Applicative. *)

Class Tupersable {rep} `{Functor t} := {
  sequenceT : forall a, rep -> t (rep * a)%type -> rep * t a
}.

Arguments sequenceT {rep t H _ a} _ _.

Arguments Tupersable rep t [H].

Definition prod_map {A B C : Type} (f : A -> B) (x : C * A) : C * B :=
  match x with (a, b) => (a, f b) end.

(****************************************************************************)

Instance Maybe_Traversable : Traversable Maybe := {
  sequence := fun _ _ A x =>
    match x with
    | Nothing => pure Nothing
    | Just x  => fmap Just x
    end
}.

Instance Maybe_Tupersable {rep} : Tupersable rep Maybe := {
  sequenceT := fun A (s : rep) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.

(****************************************************************************)

Class DSLMonad (rep : Type) (m : Type -> Type) := {
  m_is_monad       :> Monad m;
  m_is_alternative :> @Alternative m is_applicative;
  m_is_tupersable  :> @Tupersable rep m is_functor;
  m_is_traversable :> @Traversable m is_functor
}.

Program Instance Maybe_DSLMonad (rep : Type) : DSLMonad rep Maybe.

Definition DSL (rep : Type) (m : Type -> Type) `{DSLMonad rep m} (A : Type) :=
  rep -> Comp (rep * m A)%type.

Arguments DSL rep m {_} A.

Definition DSL_ (rep : Type) := Comp rep.

Program Instance DSL_Functor {rep} `{DSLMonad rep m} : Functor (DSL rep m) := {
    fmap := fun A B f (x : DSL rep m A) =>
      fun s : rep =>
        (p <- x s;
         match p with (s', m) =>
           ret (s', fmap f m)
         end)%comp
}.
Obligation 1.
  rewrite fmap_id.
  extensionality x.
  extensionality s.
  breakdown;
  destruct x0;
  try destruct x1;
  breakdown.
Qed.
Obligation 2.
  unfold compose.
  extensionality x.
  extensionality s.
  extensionality z; apply prop_ext; split; intros.
    do 4 destruct H0.
    destruct x0, x1.
    unfold Bind, Return.
    eexists.
    split.
      apply H0.
    simpl.
    rewrite <- fmap_comp_x.
    inversion H2.
    rewrite H5.
    apply H1.
  do 2 destruct H0.
  destruct x0, z.
  rewrite <- fmap_comp_x in H1.
  inversion H1.
  rewrite H4 in H1; clear H4; subst.
  unfold Bind, Return.
  eexists.
  split.
    econstructor.
    split.
      apply H0.
    simpl.
    econstructor.
  simpl.
  constructor.
Qed.

Program Instance DSL_Applicative {rep} `{DSLMonad rep m} :
  Applicative (DSL rep m) := {
  pure := fun A x => fun s : rep => (ret (s, (pure x)%monad))%comp;
  ap   := fun A B df dx => fun s : rep =>
    (p <- df s;
     match p with (s', mf) =>
       p' <- dx s';
       match p' with (s'', mx) =>
         ret (s'', mf <*> mx)
       end
     end)%comp
}.
Obligation 1. Admitted.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.

Program Instance DSL_Monad {rep} `{DSLMonad rep m} : Monad (DSL rep m) := {
  join := fun A d => fun s : rep =>
    (p <- d s; match p with (s', x) => _ end)%comp
}.
Obligation 1.
  unfold DSL in *.
  clear -s' x H.
  apply (fmap (fun f => f s')) in x.
  apply sequence in x.
  apply (fmap (sequenceT s')) in x.
  apply (fmap (prod_map join)) in x.
  assumption.
Defined.
Obligation 2. Admitted.
Obligation 3. Admitted.
Obligation 4. Admitted.
Obligation 5. Admitted.

Instance DSL_Alternative {rep} `{DSLMonad rep m} :
  @Alternative (DSL rep m) DSL_Applicative := {
  zero := fun _ => fun s : rep => ret (s, zero)
}.
Proof.                          (* implement choose *)
  intros A x y s.
  pose proof (x s) as X.
  apply (Bind X).
  intros [xs x'].
  pose proof (y s) as Y.
  apply (Bind Y).
  intros [ys y'].
  pose proof (choose (fmap (fun z => (xs, z)) x')
                     (fmap (fun z => (ys, z)) y')) as Z.
  apply (ret (sequenceT s Z)).
Defined.

Definition get {rep} `{DSLMonad rep m} : DSL rep m rep :=
  fun s => ret (s, pure s).

Definition gets {rep} `{DSLMonad rep m} {a : Type} f : DSL rep m a :=
  fun s => ret (s, pure (f s)).

Definition put {rep} `{DSLMonad rep m} (s : rep) : DSL rep m unit :=
  fun _ => ret (s, pure tt).

Definition modify {rep} `{DSLMonad rep m} (f : rep -> rep) : DSL rep m unit :=
  fun s => ret (f s, pure tt).

Definition dsl_refine {rep} `{DSLMonad rep m} {A}
  (old : DSL rep m A) (new : DSL rep m A) :=
  forall s, refine (old s) (new s).

Notation "c ≈ v" := (dsl_refine c v) (at level 90) : dsl_scope.
Notation "'ret' X" := (pure X) (at level 81) : dsl_scope.

Open Scope dsl_scope.

Definition liftC {X m rep} `{DSLMonad rep m} (c : Comp X) : DSL rep m X :=
  fun s : rep => (x <- c; Return (s, ret x))%comp.

Definition liftP {X m rep} `{DSLMonad rep m} (c : Comp (rep * X)) :
  DSL rep m X :=
  fun s : rep =>
    (p <- c;
     match p with (s', x) =>
       Return (s, ret x)
     end)%comp.

Definition liftM {X m rep} `{DSLMonad rep m} (c : m X) : DSL rep m X :=
  fun s : rep => Return (s, c)%comp.

Definition liftP2 {A B m rep} `{DSLMonad rep m} (c : Comp (A * m B)) :
  DSL rep m (A * B) :=
  fun s : rep =>
    (p <- c;
     match p with (a, mb) =>
       Return (s, fmap (fun b => (a, b)) mb)
     end)%comp.

Notation "X <- { P } ; B" := (X <- liftC (Pick (fun X => P)); B)%monad
  (at level 81, right associativity, only parsing) : monad_scope.

Definition foo {rep m} `{DSLMonad rep m} : DSL rep m nat :=
  foo <- ret 10;
  b   <- { decides b (foo < 100) };
  ret foo.

Notation "r <- 'get' rep ; X" := (r <- get; let r : rep := r in X)%monad
  (at level 81, right associativity, only parsing) : dsl_scope.

Definition mzero {A m rep} `{DSLMonad rep m} : DSL rep m A :=
  fun s : rep => Return (s, zero).

Definition guard {m rep} `{DSLMonad rep m} : bool -> DSL rep m unit :=
  fun b (s : rep) =>
    If b
    Then Return (s, pure tt)
    Else Return (s, zero).

Program Definition Guard
  {rep m T} `{DSLMonad rep m} (P : Prop) (f : DSL rep m T) :
  DSL rep m T :=
  b <- liftC { b | decides b P };
  If b
  Then f
  Else mzero.

Lemma fmap_ret `{Monad m} : forall A B (f : A -> B) (x : A),
  fmap f (ret x : m A) = ret (f x).
Proof.
Admitted.

Lemma seq_fmap `{Traversable T} `{Applicative F} :
  forall A B (f : forall {A B}, A -> B) (x : T (F A)),
    f (sequence x) = sequence (a:=B) (fmap f x).
Proof.
  intros A B f x.
Admitted.

Lemma seq_ret
  `{mA : Applicative m} `{mT : Traversable m} `{FA : Applicative F} :
  forall A (x : F A),
    @sequence m _ mT F _ _ (ret x : m (F A)) = fmap (fun y => ret y) x.
Proof.
Admitted.

Lemma seqT_ret {rep} `{Monad F} `{Tupersable rep F} :
  forall (m : Type -> Type) A (x : m A) (s s' : rep),
    sequenceT s (ret (s', x) : F (rep * m A)%type) = (s', ret x).
Proof.
Admitted.

Global Ltac because_monads' :=
  repeat (
    repeat rewrite fmap_ret;
    repeat rewrite seq_ret;
    repeat rewrite seqT_ret;
    repeat rewrite fmap_comp_x;
    repeat rewrite join_pure_x;
    simplify with monad laws
  );
  repeat rewrite fmap_ret;
  repeat rewrite seq_ret;
  repeat rewrite seqT_ret;
  repeat rewrite fmap_comp_x;
  repeat rewrite join_pure_x;
  try simplify with monad laws;
  try finish honing;
  try solve [ intuition ];
  try reflexivity;
  eauto.

Global Ltac because_monads_nosimpl := do 5 because_monads'.

Global Ltac because_monads := repeat (because_monads_nosimpl; simpl).

(****************************************************************************)

Lemma refine_match_ret :
  forall A B (xs : list B)  (a : A) (z : B -> list B -> A),
    refine (x0 <- match xs with
                  | nil => ret a
                  | cons x xs' => ret (z x xs')
                  end;
            ret x0)
           (ret (match xs with
                 | nil => a
                 | cons x xs' => (z x xs')
                 end)).
Proof.
  intros.
  induction xs; simpl;
  simplify with monad laws;
  reflexivity.
Qed.

Lemma refine_match_ret_pair :
  forall X Y Z (xs : list X) (x : Y) (y : Z)
               (z : X -> list X -> Y) (w : X -> list X -> Z),
    refine (x0 <- match xs with
                  | nil => ret (x, y)
                  | cons x xs' => ret (z x xs', w x xs')
                  end;
            ret (fst x0, snd x0))
           (ret (match xs with
                 | nil => (x, y)
                 | cons x xs' => (z x xs', w x xs')
                 end)).
Proof.
  intros.
  induction xs; simpl;
  simplify with monad laws;
  reflexivity.
Qed.
