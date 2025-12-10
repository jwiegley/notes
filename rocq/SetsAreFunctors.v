Require Export Coq.Sets.Ensembles.
Require Export Hask.Control.Monad.

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

Module CompMonadLaws.

Require Import FunctionalExtensionality.

Include MonadLaws.

Axiom prop_ext : forall (P Q : Prop), (P <-> Q) -> P = Q.

Local Transparent Bind.

Ltac breakdown :=
  try unfold id in *;
  repeat match goal with
  | [ H : ex ?X |- _ ] => destruct H
  | [ |- ssrfun.eqfun _ _ ] =>
      intro x; simpl; extensionality z; apply prop_ext; split; intros
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

Program Instance StateT_FunctorLaws : FunctorLaws Comp.
Program Instance Comp_Applicative : ApplicativeLaws Comp.
Program Instance Comp_Monad : MonadLaws Comp.
Obligation 1.
  Local Transparent ret.
  unfold id, Bind, ret.
  intro x; simpl.
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
  exists x0.
  split.
    eexists; split.
      apply H.
    unfold In in *.
    assert ((fun b : a => exists a0 : Comp a, x1 a0 /\ a0 b) z = x0 z).
      apply prop_ext; split; intros.
        breakdown.
      breakdown.
    apply f_equal2 in H2.
    rewrite H2.
    constructor.
  assumption.
Admitted.

End CompMonadLaws.

Definition DSL {S} {m} (A : Type) := S -> Comp (S * m A)%type.

Program Instance DSL_Functor {S} `{Functor m} :
  Functor DSL := {
    fmap := fun A B f (x : DSL A) =>
      fun s : S =>
        (p <- x s;
         match p with (s', m) =>
           ret (s', fmap f m)
         end)%comp
}.

Program Instance DSL_Applicative {S} `{Functor m} `{Applicative m} :
  Applicative DSL := {
  pure := fun A x => fun s : S => (ret (s, (pure x)%monad))%comp;
  ap   := fun A B df dx => fun s : S =>
    (p <- df s;
     match p with (s', mf) =>
       p' <- dx s';
       match p' with (s'', mx) =>
         ret (s'', mf <*> mx)
       end
     end)%comp
}.

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

Arguments Traversable t [H].

(* Tupersable is a specialization of Traversable that applies only to tuples,
   and thus does not require that tuples be Applicative. *)

Class Tupersable {S} `{Functor t} := {
  sequenceT : forall a, S -> t (S * a)%type -> S * t a
}.

Arguments Tupersable S t [H].

Program Instance Tuple_Functor {A} : Functor (Datatypes.prod A) := {
  fmap := fun A B f x => match x with (a, b) => (a, f b) end
}.

(* Require Import Hask.Data.Monoid. *)

(* Program Instance Tuple_Applicative {A} `{Monoid A} : *)
(*   Applicative (Datatypes.prod A) := { *)
(*   ap := fun A B mf mx => *)
(*     match mf with (a, f) => *)
(*       match mx with (b, x) => *)
(*         (mappend a b, f x) *)
(*       end *)
(*     end *)
(* }. *)

Program Instance DSL_Monad {S}
  `{Functor m} `{Applicative m} `{Monad m}
  `{Traversable m} `{Tupersable S m} :
  Monad DSL := {
  join := fun A d => fun s : S =>
    (p <- d s;
     match p return Comp (S * m A) with (s', x) => _ end)%comp
}.
Obligation 1.
  unfold DSL in *.
  clear -s' x H H0 H1 H2 H3 H4 H5.
  apply (fmap (fun f => f s')) in x.
  apply sequence in x.
  apply (fmap (sequenceT _ s')) in x.
  apply (fmap (fmap join)) in x.
  assumption.
Defined.

Definition get {S} `{Applicative m} : @DSL S m S :=
  fun s => ret (s, pure s).

Definition gets {S} `{Applicative m} {a : Type} f : @DSL S m a :=
  fun s => ret (s, pure (f s)).

Definition put {S} `{Applicative m} (s : S) : @DSL S m unit :=
  fun _ => ret (s, pure tt).

Definition modify {S} `{Applicative m} (f : S -> S) : @DSL S m unit :=
  fun s => ret (f s, pure tt).

Definition dsl_refine {S} {m} {A} (old : @DSL S m A) (new : @DSL S m A) :=
  forall s, refine (old s) (new s).

Notation "c ≈ v" := (dsl_refine c v) (at level 90) : dsl_scope.
Notation "'ret' X" := (pure X) (at level 81) : dsl_scope.

Require Export Hask.Data.Maybe.

Instance Maybe_Traversable : Traversable Maybe := {
  sequence := fun _ _ A x =>
    match x with
    | Nothing => pure Nothing
    | Just x  => Just <$> x
    end
}.

Instance Maybe_Tupersable {S} : Tupersable S Maybe := {
  sequenceT := fun A (s : S) x =>
    match x with
    | Nothing => (s, Nothing)
    | Just (s', x)  => (s', Just x)
    end
}.

Open Scope comp_scope.

Definition lift {X S} (c : Comp X) : DSL X :=
  fun s : S => x <- c; Return (s, Just x).

Close Scope comp_scope.

Definition mzero {A S} : DSL A :=
  fun s : S => Return (s, Nothing).

Program Definition Guard {T S} (P : Prop) (f : @DSL S _ T) : @DSL S _ T :=
  b <- lift { b | decides b P };
  If b
  Then f
  Else mzero.
