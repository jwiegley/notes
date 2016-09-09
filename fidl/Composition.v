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

Definition comp_prod `{Monad m} {A} (X : m (Comp (m A))) : Comp (m A).
Admitted.

Instance mComp_Monad_Distributes `{Monad m} : @Monad_Distributes Comp _ m _ := {
  prod := @comp_prod _ _
}.

Import MonadLaws.

Global Program Instance mComp_Monad_DistributesLaws `{Monad m} :
  @Monad_DistributesLaws Comp _ m _ mComp_Monad_Distributes.
Obligation 1.
Admitted.
Obligation 2.
Admitted.
Obligation 3.
Admitted.
Obligation 4.
Admitted.
Obligation 5.
Admitted.

Instance mComp_Monad `{Monad m} : Monad (CompT m) := Compose_Monad.

Definition liftC {A} `{Monad m} : Comp A -> CompT m A := fmap pure.
Definition liftM {A} `{Monad m} : m A    -> CompT m A := pure.

Require Import Compare_dec.

Axiom random_action : forall `{Monad m}, m unit.

Definition example `{Monad m} : CompT m nat :=
  n <- liftC { n | n > 0 };
  when (leb n 10)
    (liftM random_action) ;;
  liftC (ret (n + 10)).

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

Corollary prod_pure_x `{Monad_DistributesLaws M N} :
  forall A x, prod M N A (pure[N] x) = x.
Proof.
  intros.
  replace (prod M N A ((pure[N]) x)) with ((prod M N A \o (pure[N])) x).
    rewrite prod_pure.
    reflexivity.
  reflexivity.
Qed.

Corollary prod_fmap_pure_x `{Monad_DistributesLaws M N} :
  forall A x, prod M N A (fmap[N] (pure[M \o N]) x) = pure[M] x.
Proof.
  intros.
  replace (prod M N A (fmap[N] (pure[(M \o N)]) x))
    with ((prod M N A \o fmap[N] (pure[(M \o N)])) x).
    rewrite prod_fmap_pure.
    reflexivity.
  reflexivity.
Qed.

Definition example_refined `{MonadLaws m} :
    { f : m nat | refine example (ret f) }.
Proof.
  eexists.
  unfold example.
  unfold bind, comp.
  simpl.
  simplify with monad laws.
  refine pick val 15.
    simplify with monad laws.
    unfold id.
    rewrite fmap_pure_x.
    simpl.
    unfold return_.
    simpl.
    pose proof (@prod_pure_x _ _ _ _ _ mComp_Monad_DistributesLaws nat).
    simpl in H1.
    rewrite H1.
    simplify with monad laws.
    unfold liftC.
    rewrite fmap_pure_x.
    rewrite H1.
    simpl.
    simplify with monad laws.
    finish honing.
  omega.
Defined.

Eval simpl in projT1 example_refined.

Definition example_refined' `{MonadLaws m} :
  { f : m nat | refine example (ret f) }.
Proof.
  eexists.
  unfold example.
  unfold bind, comp.
  simpl.
  simplify with monad laws.
  refine pick val 5.
    simplify with monad laws.
    unfold id.
    rewrite fmap_pure_x.
    pose proof (@prod_pure_x _ _ _ _ _ mComp_Monad_DistributesLaws nat).
    simpl in H1.
    rewrite H1.
    simplify with monad laws.
    unfold liftC.
    simpl.
    pose proof (@prod_fmap_pure_x _ _ _ _ _ mComp_Monad_DistributesLaws nat).
    unfold comp in H2.
    simpl in H2.
    unfold comp in H2.
    replace (fun _ : () => (v <- ret 15;
                                 ret ((pure[m]) v))%comp)
      with (fun _ : () => (ret (pure[m] 15))%comp).
Abort.

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
  @Monad_DistributesLaws Comp _ m _ mComp_Monad_Distributes.
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

Program Instance mComp_MonadLaws `{MonadLaws m} : MonadLaws (CompT m) :=
  MonadLaws_Compose (M:=Comp) (N:=m).

End CompTLaws.