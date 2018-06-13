Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.
Require Export Hask.Control.Monad.

Generalizable All Variables.

Inductive UnionF (a : Type) : list (Type -> Type) -> Type :=
  | UOr  : forall t r, t a + UnionF a r -> UnionF a (t :: r).

Definition Union (r : list (Type -> Type)) (a : Type) := UnionF a r.

Class Member (t : Type -> Type) (r : list (Type -> Type)) := {
  inj : forall v, t v -> Union r v;
  prj : forall v, Union r v -> option (t v)
}.

Arguments inj {t r _ v} _.
Arguments prj {t r _ v} _.

Program Definition decomp `(u : Union (t :: r) v) : t v + Union r v :=
  match u in UnionF _ xs return (t :: r)%list = xs -> t v + Union r v with
  | UOr _ _ _ x => fun _ => _ x
  end eq_refl.

Inductive Freer (f : Type -> Type) (a : Type) :=
  | Pure : a -> Freer f a
  | Impure : forall x, f x -> (x -> Freer f a) -> Freer f a.

Arguments Pure {f a} _.
Arguments Impure {f a x} _ _.

Fixpoint Freer_map {r} `(f : a -> b) (x : Freer r a) : Freer r b :=
  match x with
  | Pure v => Pure (f v)
  | Impure u k => Impure u (fun x => Freer_map f (k x))
  end.

Program Instance Freer_Functor (f : Type -> Type) : Functor (Freer f) := {
  fmap := @Freer_map _
}.

Fixpoint Freer_ap {r} `(f : Freer r (a -> b)) (x : Freer r a) : Freer r b :=
  match f, x with
  | Pure f, Pure v     => Pure (f v)
  | Pure f, Impure u k => Impure u (fun x => Freer_map f (k x))
  | Impure u k, m      => Impure u (fun x => Freer_ap (k x) m)
  end.

Program Instance Freer_Applicative (f : Type -> Type) : Applicative (Freer f) := {
  pure := fun _ => Pure;
  ap := fun _ _ => Freer_ap
}.

Fixpoint Freer_join {r} `(f : Freer r (Freer r a)) : Freer r a :=
  match f with
  | Pure v     => v
  | Impure u k => Impure u (fun x => Freer_join (k x))
  end.

Program Instance Freer_Monad (f : Type -> Type) : Monad (Freer f) := {
  join := @Freer_join _
}.

Module FreerLaws.

Include MonadLaws.

Require Import FunctionalExtensionality.

Program Instance Freer_FunctorLaws (f : Type -> Type) : FunctorLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold id.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x; simpl; auto.
  unfold comp.
  f_equal; simpl.
  extensionality y.
  apply H.
Qed.

Program Instance Freer_ApplicativeLaws (f : Type -> Type) : ApplicativeLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  specialize (H y).
  destruct (f1 y); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction w, u, v; simpl; auto.
Admitted.                       (* exercise for the reader! ;) *)
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  induction u; auto.
  f_equal.
  extensionality x0.
  specialize (H x0).
  destruct (f1 x0); auto.
Qed.
Next Obligation.
  unfold Freer_ap, Freer_map, comp; simpl; auto.
  extensionality x0.
  destruct x0; auto.
Qed.

Program Instance Freer_MonadLaws (f : Type -> Type) : MonadLaws (Freer f).
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.
Next Obligation.
  extensionality x.
  induction x;
  unfold Freer_join, Freer_map, comp; simpl; auto.
  unfold id.
  f_equal.
  extensionality y.
  apply H.
Qed.

End FreerLaws.

Fixpoint injF `{Member eff r} `(f : Freer eff a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure f k => Impure (inj f) (fun x => injF (k x))
  end.

Polymorphic Inductive Get (e : Type) : Type -> Type := Ask : Get e e.

Arguments Ask {e}.

Definition ask {e : Type} : Freer (Get e) e :=
  Impure Ask Pure.

Fixpoint runReader `(x : e) `(f : Freer (Get e) a) : a :=
  match f with
  | Pure v => v
  | Impure Ask k => runReader x (k x)
  end.

Inductive Put (o : Type) : Type -> Type :=
  | Tell : o -> Put o unit.

Arguments Tell {o} _.

Definition send `(t : f a) : Freer f a := Impure t Pure.

Definition tell `(x : o) : Freer (Put o) unit := send (Tell x).

Fixpoint runWriter `(f : Freer (Put o) a) : (list o * a) :=
  match f with
  | Pure v => (nil, v)
  | Impure (Tell x) k =>
      let '(l, v) := runWriter (k tt) in (x::l, v)%list
  end.

Program Fixpoint runReaderC `(x : e) `(f : Freer (Union (Get e :: r)) a) : Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runReaderC x (k _)
    | inr u => Impure u (fun y => runReaderC x (k y))
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.

Program Fixpoint runWriterC `(f : Freer (Union (Put o :: r)) a) : Freer (Union r) (list o * a) :=
  match f with
  | Pure v => Pure (nil, v)
  | Impure u k =>
    match decomp u with
    | inl f =>
      res <- runWriterC (k _) ;
      let '(l, v) := res in
      pure (_ :: l, v)%list
    | inr u => Impure u (fun x => runWriterC (k x))
    end
  end.
Next Obligation.
  destruct f.
  exact o0.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

Program Definition run `(f : Freer (Union nil) a) : a :=
  match f with
  | Pure x => x
  | Impure u k => False_rect _ _
  end.
Next Obligation.
  (* there are no more choices: effects are not possible *)
  inversion u.
Qed.

Program Fixpoint runState {e : Type} (x : e)
        `(f : Freer (Union (Get e :: Put e :: r)%list) a) :
  Freer (Union r) a :=
  match f with
  | Pure v => Pure v
  | Impure u k =>
    match decomp u with
    | inl f => runState x (k _)
    | inr u =>
      match decomp u with
      | inl f => runState x (k _)
      | inr u => Impure u (fun y => runState x (k y))
      end
    end
  end.
Next Obligation.
  destruct f.
  exact x.
Defined.
Next Obligation.
  destruct f.
  exact tt.
Defined.

Inductive Choice : Type -> Type :=
  | Pick : forall A (P : A -> Prop), Choice A.

Arguments Pick {_} _.

Definition Eff (r : list (Type -> Type)) (a : Type) := Freer (Union r) a.

Program Instance Functor_Eff {r} : Functor (Eff r) := Freer_Functor _.
Program Instance Applicative_Eff {r} : Applicative (Eff r) := Freer_Applicative _.
Program Instance Monad_Eff {r} : Monad (Eff r) := Freer_Monad _.

Definition computes_to {A : Type} (ca : A -> Prop) (a : A) : Prop := ca a.

Notation "c ↝ v" := (computes_to c v) (at level 40).

Import EqNotations.

(* A Choice "effect" may be refined so long as every value computable from the
   new choice was computable from the original choice. *)
Definition refineChoice {a} (old new : Choice a) : Prop :=
  match old in Choice x return x = a -> _ with
  | Pick o => fun Ho =>
    match new in Choice y return y = a -> _ with
    | Pick n => fun Hn =>
      forall v, n ↝ v -> o ↝ rew <- Ho in rew Hn in v
    end eq_refl
  end eq_refl.

Program Fixpoint refine {r a} (old new : Eff (Choice :: r) a) : Prop :=
  match old, new with
  | Pure x,       Pure y       => x = y
  | Pure x,       Impure u k   => False
  | Impure u k,   Pure y       =>
    match decomp u with
    | inl f => refineChoice f (_ (Pick (Singleton _ y)))
    | inr u => refine (Impure u k) new
    end
  | Impure xu xk, Impure yu yk => _
    match decomp xu, decomp yu with
    | inl f, inl g => refineChoice f (_ g)
    | inl f, inr g => _
    | inr f, inl g => _
    | inr f, inr g => True
    end
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Fixpoint choose `(f : Eff (Choice :: r) a) : Eff r a :=
  match f with
  | Pure x => Pure x
  | Impure u k =>
    match decomp u with
    | inl f => choose (k _)
    | inr u => Impure u (fun y => choose (k y))
    end
  end.
Next Obligation.
  destruct f.
Admitted.
