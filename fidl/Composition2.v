Require Import
  Hask.Control.Applicative
  Hask.Control.Monad
  FIDL.Tactics
  FIDL.Comp.

Definition deterministic {A} (c : Comp A) : Type :=
  { x : A | c = ret x }%type.
Arguments deterministic {A} c /.

Definition CompT (m : Type -> Type) (A : Type) := Comp (m A).

Instance mComp_Functor `{Functor m} : Functor (CompT m) := Compose_Functor.

Instance mComp_Applicative `{Applicative m} : Applicative (CompT m) :=
  @Compose_Applicative Comp m _ _.

Instance mComp_Alternative `{Alternative m} : Alternative (CompT m) :=
  Compose_Alternative (F:=Comp) (G:=m).

Import MonadLaws.

Require Import Compare_dec.

Axiom random_action : forall `{Monad m}, m unit.

Definition example `{Monad m} (rep : m unit) : Comp (m unit * nat) :=
  n    <- { n | n > 0 };
  rep' <- { r | (n <= 10 /\ r = random_action) \/
                (n  > 10 /\ r = pure tt) };
  ret (rep', n + 10).

Require Import
  Fiat.ADT
  Fiat.ADTNotation
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Lemma refine_computes : forall A (c : Comp A) v, refine c (ret v) <-> c ↝ v.
Proof.
  intros.
  split; intros.
    apply H.
    reflexivity.
  unfold refine.
  intros.
  inversion H0; subst.
  exact H.
Qed.

Definition example_refined `{MonadLaws m} :
    { f : m unit | exists n, refine (example (pure tt)) (ret (f, n)) }.
Proof.
  eexists.
  unfold example.
  unfold bind, comp.
  simpl.
  eexists.
  simplify with monad laws.
  refine pick val 15.
    simplify with monad laws.
    unfold id.
    refine pick val (pure[m] tt).
      simplify with monad laws.
      finish honing.
    right.
    intuition.
  omega.
Defined.

Eval simpl in projT1 example_refined.

Module CompTLaws.

Import MonadLaws.
Import CompLaws.

Instance mComp_FunctorLaws `{FunctorLaws m} : FunctorLaws (CompT m) :=
  FunctorLaws_Compose.

Instance mComp_ApplicativeLaws `{ApplicativeLaws m} :
  ApplicativeLaws (CompT m) := @ApplicativeLaws_Compose Comp _ _ m _ _.

Local Obligation Tactic := idtac.

Program Instance mComp_Monad_DistributesLaws `{MonadLaws m} :
  @Monad_DistributesLaws m _ Comp Comp_Applicative mComp_Monad_Distributes.
Obligation 1.
  intros.
  simpl prod.
Admitted.
Obligation 2.
  intros.
  simpl prod.
Admitted.
Obligation 3.
  intros.
  simpl prod.
Admitted.
Obligation 4.
Admitted.

(* Program Instance mComp_MonadLaws `{MonadLaws m} : MonadLaws (CompT m) := *)
(*   MonadLaws_Compose (M:=m) (N:=Comp). *)

End CompTLaws.