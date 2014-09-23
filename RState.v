Require Export Coq.Init.Datatypes.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import FunctionalExtensionality.
(* Require Export Endo. *)
(* Require Export Applicative. *)
(* Require Export Monad. *)
Require Import Recdef.

Open Scope program_scope.

Definition compose_dep {A B C}
  (f : forall x : B, C x) (g : A -> B) (x : A) : C (g x) := f (g x).

Class DepFunctor {A} (F : (A -> Type) -> Type) :=
{ dep_fobj := F
; dep_fmap : forall {X Y}, (forall B, X B -> Y B) -> F X -> F Y

; dep_fun_identity : forall {X}, dep_fmap (fun _ => @id X) = id
; dep_fun_composition : forall {X Y Z}
    (f : forall B, Y B -> Z B) (g : forall B, X B -> Y B),
    dep_fmap f ∘ dep_fmap g = dep_fmap (fun b => f b ∘ g b)
}.

Reserved Notation "f <*> g" (at level 28, left associativity).

Class DepApplicative {A} (F : (A -> Type) -> Type) :=
{ is_dep_functor :> DepFunctor F

; dep_pure : forall {X}, X -> F (fun _ => X)
; dep_ap : forall {X Y}, F (fun _ => forall b, X b -> Y b) -> F X -> F Y
    where "f <*> g" := (dep_ap f g)

; app_identity : forall {X}, dep_ap (dep_pure (fun _ => @id X)) = id
(*
; app_composition
    : forall {X Y Z} (v : F (fun _ => forall b, X b -> Y b))
             (u : F (fun _ => forall b, Y b -> Z b)) (w : F X),
    dep_pure (fun _ => compose) <*> u <*> v <*> w = u <*> (v <*> w)
*)
; app_homomorphism : forall {X Y} (x : X) (f : X -> Y),
    dep_pure (fun _ => f) <*> dep_pure x = dep_pure (f x)
(*
; app_interchange : forall {X} {Y : A -> Type} (y : X)
    (u : F (fun _ => forall b, X -> Y b)),
    u <*> dep_pure y = dep_pure (fun _ f => f y) <*> u
*)

; app_fmap_unit : forall {X Y} (f : X -> Y),
    dep_ap (dep_pure (fun _ => f)) = dep_fmap (fun _ => f)
}.

Class DepMonad {A} (M : (A -> Type) -> Type) :=
{ is_dep_applicative :> DepApplicative M

; dep_join : forall {X}, M (fun _ => M X) -> M X

; monad_law_1 : forall {X},
  dep_join ∘ dep_fmap (fun _ => dep_join) = (@dep_join X) ∘ dep_join
; monad_law_2 : forall {X},
  dep_join ∘ dep_fmap (fun _ => (@dep_pure _ M is_dep_applicative X)) = id
; monad_law_3 : forall {X}, (@dep_join X) ∘ dep_pure = id
; monad_law_4 : forall {X Y} (f : X -> Y),
  dep_join ∘ dep_fmap (fun _ => dep_fmap (fun _ => f)) =
  dep_fmap (fun _ => f) ∘ dep_join
}.

Section RState.

Variable   s : Type.
Hypothesis P : relation s.
Context  `(e : PreOrder s P).

Record StateP (before : s) (a : s -> Type) := {
    after  : s;
    result : a after;
    holds  : P before after
}.

Arguments after [before] [a] _.
Arguments result [before] [a] _.
Arguments holds [before] [a] _.

(** The [RState] monad requires that a given equivalence relation hold
    between state transitions. *)
Inductive RState (a : s -> Type) : Type :=
  | St : (forall st : s, StateP st a) -> RState a.

Arguments St [a] _.

Definition runRState {a : s -> Type} (v : RState a)
  : forall st : s, StateP st a :=
      match v with St f => fun st => f st end.

Definition RState_fmap (a b : s -> Type)
  (f : forall st : s, a st -> b st) (x : RState a) : RState b :=
  St (fun st =>
        let sp := runRState x st in
        {| after  := after sp
         ; result := f (after sp) (result sp)
         ; holds  := holds sp
         |}).

Hint Unfold RState_fmap.

Ltac RState_auto :=
  intros; simpl;
  repeat (
    autounfold; unfold id, compose; simpl;
    f_equal; try apply proof_irrelevance; auto;
    match goal with
    | [ |- (fun _ : RState _ => _) = (fun _ : RState _ => _) ] =>
        extensionality sx
    | [ |- (fun _ : s => _) = _ ] =>
        extensionality st
    | [ st : s, sp : forall st : s, StateP st _ |- _ ] =>
        destruct (sp st)
    | [ sx : RState _ |- _ ] => destruct sx as [sp]
    | [ |- St _ = St _ ] => f_equal
    end).

Obligation Tactic := RState_auto.

Program Instance RState_Functor : DepFunctor RState := {
    dep_fmap := RState_fmap
}.

Definition RState_pure (a : Type) (x : a) : RState (const a) :=
  St (fun st =>
        {| after  := st
         ; result := x
         ; holds  := reflexivity st
         |}).

Hint Unfold RState_pure.

Definition RState_ap (a b : s -> Type)
  (f : RState (fun _ => forall st, a st -> b st)) (x : RState a) : RState b :=
  St (fun st =>
        let spf := runRState f st in
        let spx := runRState x (after spf) in
        {| after  := after spx
         ; result := (result spf) (after spx) (result spx)
         ; holds  := transitivity (holds spf) (holds spx)
         |}).

Hint Unfold RState_ap.

Program Instance RState_Applicative : DepApplicative RState := {
    dep_pure := RState_pure;
    dep_ap   := RState_ap
}.

Definition RState_join (a : s -> Type) (x : RState (fun _ => RState a))
  : RState a :=
  St (fun st =>
        let sp := runRState x st in
        let sp' := runRState (result sp) (after sp) in
        {| after  := after sp'
         ; result := result sp'
         ; holds  := transitivity (holds sp) (holds sp')
         |}).

Hint Unfold RState_join.

Program Instance RState_Monad : DepMonad RState := {
    dep_join := RState_join
}.

Definition get : RState (fun _ => s) :=
  St (fun st =>
        {| after  := st
         ; result := st
         ; holds  := reflexivity st
         |}).

(** There cannot be a definition of [put], since we can only lawfully
    transform the state, not simply replace it.  Therefore, [modify] must be
    used in all cases where [put] would ordinarily have been. *)
Definition modify (f : forall st : s, { st' : s & P st st' })
  : RState (const unit) :=
  St (fun st =>
        let (st', H) := f st in
        {| after  := st'
         ; result := tt
         ; holds  := H
         |}).

End RState.