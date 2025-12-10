Require Import Hask.Prelude.
Require Import Hask.Control.Category.

Generalizable All Variables.

Definition HyperF (a b r : Type) := (r -> a) -> b.
Arguments HyperF a b r /.
Definition μ (F : Type -> Type) := forall a, (F a -> a) -> a.
Arguments μ F /.
Definition Hyper (a b : Type) := μ (HyperF a b).
Arguments Hyper a b /.

Definition invoke `(h : Hyper a b) : Hyper b a -> b.
Proof.
  move=> k.
  apply h.
  apply => x.
  apply k.
  apply => y.
  by apply h.
Defined.

Definition combine `(f : a -> b) (q : Hyper a b) : Hyper a b.
Proof.
  move=> r /=.
  apply => k.
  rewrite /= in q.
  specialize (q r).
  apply (f \o k).
  apply q.                      (* stuck *)
Admitted.

Definition base {b} `(x : a) : Hyper b a.
Proof.
  simpl.
  move=> c /=.
  apply.
  exact: const x.
Defined.

Definition project `(h : Hyper a b) : a -> b.
Proof.
  move=> x.
  have B := (base x).
  apply: (B a b) => /= k.
  apply h.
  by apply.
Defined.

Definition lift `(f : a -> b) : Hyper a b.
Proof.
  move=> r.
  apply => /= k.
  apply (f \o k).               (* stuck *)
Admitted.

Definition compose `(f : Hyper b c) `(g : Hyper a b) : Hyper a c.
Proof.
  move=> /= r.
  apply => k.
  apply f.
  apply => x.
  apply g.
  apply => y.
  apply k.                      (* stuck *)
Admitted.

Definition self {a} : Hyper a a := lift id.
