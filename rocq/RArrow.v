Require Export Coq.Init.Datatypes.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Import Coq.Structures.Orders.
Require Import FunctionalExtensionality.
Require Export Endo.
Require Export Applicative.
Require Export Monad.
Require Import Recdef.

Open Scope program_scope.
Close Scope nat_scope.

Section Arrows.

Variable a : forall {b : Type} (x : b), (b -> Type) -> Type.

Class Arrow : Type := {
    compose_fwd  (f : a b c) (g: forall x : b, a (c x) d) (x : b) : a b d := f (g x).

    first : forall {b c d}, a b c
      -> a (b * d) (fun p => let (b,_) := p in c b * d);
    second : forall {b c d}, a b c
      -> a (d * b) (fun p => let (_,b) := p in d * c b);
    fork : forall {b b' c c'}, a b c -> a b' c'
      -> a (b * b') (fun p => let (b,b') := p in c b * c' b');
    fanout : forall {b c c'}, a b c -> a b c'
      -> a b (fun b => c b * c' b)
}.

Infix "***" := fork (at level 28, left associativity).
Infix "&&&" := fanout (at level 28, left associativity).

Class ArrowZero `{Arrow} : Type := {
    zeroArrow : forall {b c}, a b c
}.

Class ArrowPlus `{ArrowZero} : Type := {
    aplus : forall {b c}, a b c -> a b c -> a b c
}.

Infix "<+>" := aplus (at level 27, right associativity).

Class ArrowChoice `{Arrow} : Type := {
    left : forall {b c d}, a b c
      -> a (b + d) (fun p => match p with
                             | inl b => c b
                             | inr _ => d
                             end);
    right : forall {b c d}, a b c
      -> a (d + b) (fun p => match p with
                             | inl _ => d
                             | inr b => c b
                             end);
    split : forall {b b' c c'}, a b c -> a b' c'
      -> a (b + b') (fun p => match p with
                             | inl b => c b
                             | inr b => c' b
                             end);
    fanin : forall {b c d}, a b (fun b => d (inl b))
      -> a c (fun b => d (inr b)) -> a (b + c) d
}.

Infix "+++" := split (at level 28, left associativity).
Infix "|||" := fanin (at level 28, left associativity).

Class ArrowApply `{Arrow} : Type := {
    app : forall {b c}, a (a b c * b) (fun x => let (_,b) := x in c b)
}.

Definition compose_dep {A B C}
  (f : forall x : B, C x) (g : A -> B) (x : A) : C (g x) := f (g x).

Definition acompose_fwd {b c d}
  (f : a b c) (g: forall x : b, a (c x) d) (x : b) : a b d := f (g x).

Inductive ArrowMonad (b : Type) :=
  | mkArrowMonad : a unit (const b) -> ArrowMonad b.

Global Program Instance ArrowMonad_Functor : Functor ArrowMonad := {
    fmap := fun f x => match x with
      mkArrowMonad m => mkArrowMonad (m >>> arr f)
      end
}.

End Arrows.
