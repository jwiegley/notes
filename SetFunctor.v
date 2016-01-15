Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Data.Functor.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Monad.
Require Import Coq.Sorting.Sorted.

Require Import mathcomp.ssreflect.path.

Generalizable All Variables.

Inductive Compare := Lt | Eq | Gt.

Class Ord (a : Type) := {
  compare : a -> a -> Compare
}.
Arguments compare {a _} _ _.

Definition is_lt `{Ord a} :=
  fun x y : a => if compare x y is Lt then true else false.

Record OrdSet (a : eqType) := {
  carrier       : seq a;
  always_sorted : forall `{Ord a}, sorted is_lt carrier;
  always_uniq   : uniq carrier      (* uses the eqType *)
}.

Section OrdMonad.

Context {LookupOrd : forall a, Ord a}.

Program Instance OSet_Functor : Functor OrdSet.
Obligation 1.
  
  destruct X0.
  fmap := fun A B f x =>
    
            undup \o sortBy (@is_lt _ (LookupOrd B)) \o map f
}.

Program Instance OSet_Applicative : Applicative OSet := {
  pure := fun _ x => [:: x];
  ap   := fun A B mf mx =>
    (undupEq \o @sortEq B (LookupOrd B) \o flatten \o map (fmap ^~ mx)) mf
}.

Program Instance OSet_Monad : Monad OSet := {
  join := fun A => undupEq \o @sortEq A (LookupOrd A) \o flatten
}.

End OrdMonad.

Module OrdMonadLaws.

Require Import FunctionalExtensionality.

Include ListLaws.

Context {LookupOrd : forall a, Ord a}.

Program Instance OSet_FunctorLaws : @FunctorLaws OSet (@OSet_Functor LookupOrd).
Obligation 1.
  move=> x /=.
  rewrite map_id.
  elim=> [|x xs IHxs] //=.
  simpl in IHxs.
  rewrite /sortEq.
  move=> x.
  induction x
  unfold 

Program Instance OSet_ApplicativeLaws :
    @ApplicativeLaws OSet (@OSet_Applicative LookupOrd).

Program Instance OSet_MonadLaws : @MonadLaws OSet (@Set_Monad LookupOrd).

End OrdMandLaws.