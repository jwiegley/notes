Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Free.
Require Import Hask.Control.Monad.Free.
Require Import Hask.Data.Either.
Require Import Coq.Strings.String.

Open Scope string_scope.

Generalizable All Variables.

Inductive A r :=
  | Alpha : r -> A r.

Program Instance A_Functor : Functor A := {
  fmap := fun _ _ f x => match x with
    | Alpha _ r => Alpha _ (f r)
    end
}.

Inductive B r :=
  | Beta : r -> B r.

Program Instance B_Functor : Functor B := {
  fmap := fun _ _ f x => match x with
    | Beta _ r => Beta _ (f r)
    end
}.

Definition Sum (A B : Type -> Type) `{Functor A} `{Functor B} :=
  (fun t => (A t + B t)%type).

Definition FA   := Free A.

Definition alpha : FA unit := liftF (Alpha _ tt).

Definition FA_example_term : FA unit :=
  alpha ;; alpha ;; alpha.

Definition FB   := Free B.

Definition beta  : FB unit := liftF (Beta _ tt).

Definition FB_example_term : FB unit :=
  beta ;; beta ;; beta.

Definition FA_B := Free (Sum A B).

Definition alphaA_B : FA_B unit := liftF (inl (Alpha _ tt)).
Definition betaA_B  : FA_B unit := liftF (inr (Beta _ tt)).

(* Interesting to note: Sum is a Functor, but not a Monad, yet Free of Sum is
   freely a monad. *)
Program Instance Sum_Functor
        (F G : Type -> Type) `{Functor F} `{Functor G} :
  Functor (Sum F G) := {
  fmap := fun A B f x =>
    match x with
    | inl x => inl (fmap f x)
    | inr x => inr (fmap f x)
    end
}.

Definition FA_B_example_term : FA_B unit :=
  alphaA_B ;; betaA_B ;; alphaA_B.

(*****************************************************************************
 THE QUESTION

 Can I add a term to [B], such that within the grammar [FB], use of this term
 allows the sub-grammar [FA_B] to follow -- and only then.

 For example, these would be illegal:

   alpha'
   beta ;; alpha'

 But this would be legal:

   beta ;; betaSub alpha' ;; beta

 Here's a naive way to do it:

 *****************************************************************************)

Inductive B' r :=
  | Beta' : r -> B' r
  | BetaSub' : FA_B r -> B' r.

Program Instance B'_Functor : Functor B' := {
  fmap := fun _ _ f x => match x with
    | Beta'    _ r => Beta' _ (f r)
    | BetaSub' _ r => BetaSub' _ (fmap f r)
    end
}.

Definition FB' := Free B'.

Definition beta' : FB' unit := liftF (Beta' _ tt).
Definition betaSub' `(term : FA_B a) : FB' a := liftF (BetaSub' _ term).

Definition FB'_example_term : FB' unit :=
  beta' ;; betaSub' alphaA_B ;; beta'.

(*****************************************************************************
 THE PROBLEM WITH THE NAIVE APPROACH

 The beauty of using [Free] to generate our grammars is that we can freely
 switch to effect-carrying grammars by using [FreeT] instead, with no change
 to our base functors. However, the encoding of [B'] above bakes in an
 effectless FA_B, since it was generated from [Free] and not [FreeT].

 What I need, it seems, is to parameterize my use of FA_B over the type of
 free generator that is to be used, while not knowing which [Monad] will be
 used at evaluation/term construction time.

 Here's the horrible version:

 *****************************************************************************)

Inductive BT `{Monad m} r :=
  | BetaT : r -> BT r
  | BetaSubT : FreeT (Sum A B) m r -> BT r.

(* By chosing [m] to be the [Identity], I can recover the non-effect bearing
   version. However, now I have to express [m] everywhere in my terms, even
   though it has nothing to do with our definition. This is something that our
   constructor or our evaluator should be choosing, and not the grammar
   definition.

   So what if I parameterize this, to remove the [m]? Then I lose the ability
   to ever construct terms with effects in [m]: *)

Inductive BP p r :=
  | BetaP : r -> BP p r
  | BetaSubP : p (Sum A B) r -> BP p r.

Definition FBP := Free (BP Free).

Definition betaSubP `(term : FA_B a) : FBP a := liftF (BetaSubP _ _ term).

Definition foo (f : nat -> string) (g : list nat -> string) :
  Teletype nat string unit :=
  a <- liftF (Get id);
  b <- liftF (GetMany (fun k => k _ nil (@cons _)));
  liftF (Put (f a) tt) ;;
  liftF (Put (g b) tt).

Definition TeletypeT a b := FreeT (TeletypeF a b).

Require Import Hask.Control.Monad.Trans.Free.

Definition bar (f : nat -> string) (g : list nat -> string) `{Monad m} :
  TeletypeT nat string m unit :=
  a <- liftF (Get id);
  b <- liftF (GetMany (fun k =>
          k (m (list nat)) (return_ nil)
            (fun (a : nat) rest => cons a <$> rest)));
  b' <- liftFM b;
  liftF (Put (f a) tt) ;;
  liftF (Put (g b') tt).

Definition phi `{Monad m} `(x : TeletypeF nat string (m r)) : m r :=
  match x with
  | Get k     => k 0
  | GetMany k => k (fun _ z f =>
                      x <- f 0 z;
                      f 1 x)
  | Put b r   => r
  end.

Definition eval {r} := iter (phi (r:=r)).
Definition evalT {r} := iterT (phi (r:=r)).
