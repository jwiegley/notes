Require Import
  Coq.Vectors.Vector
  Hask.Control.Monad.Free
  Fiat.Common.ilist
  FIDL.Tactics
  FIDL.Comp.

Generalizable All Variables.

Import VectorNotations.

(* A set of [Effects] is a fixed size list of functors, representing the
   various effect algebras that may be used within a computation. *)
Definition Effects := Vector.t (Type -> Type).

(* An [EffList] is a vector of indices into an [Effects] vector. *)
Definition EffList `(es : Effects n) := Vector.t (Fin.t n).
Definition EffectsOf `(_ : EffList (n:=n) es o) := es.

(* A [Union] is an ilist, where the type of every member is from [es]. *)
Definition Union `(es : Effects n) `(r : EffList es o) (a : Type) :=
  ilist (A:=Fin.t n) (B:=fun n => nth es n a) r.

Definition Eff `(r : EffList (n:=n) es o) := Free (Union r).

Inductive Comp (e : Type -> Type) `(r : EffList (n:=n) es o) (a b : Type) :=
  | Value   : a -> Comp e r a b
  | Further : e (Eff r b) -> Comp e r a b.

Definition Handler e `(r : EffList (n:=n) es o) a b :=
  Comp e r a b -> Eff r b.

Definition Handles (f : Type -> Type) `(es : Effects n) : Prop :=
  Vector.In f es.

Inductive Abortive (a : Type) :=
  | Exit : a -> Abortive a.

Require Import mathcomp.ssreflect.ssreflect.

Lemma unhandled_effect :
  forall (e : Type -> Type)
         (es : Effects 0),
         Handles e es -> False.
Proof.
  intros.
Admitted.

Program Definition abort `(r : EffList (n:=n) es o) :
  Handles Abortive es -> Eff r () :=
  (* fun _ => Join Pure (icons (Exit ()) inil). *)
  fun _ => Join Pure _.
Obligation 1.
  generalize dependent r.
  generalize dependent o.
  induction n.
    intros.
    apply unhandled_effect in H.
    contradiction.
  intros.
Admitted.

(*
Definition foo {a} `{Monad m} : Handles Abortive r -> CompT r m a :=
  abort.
*)