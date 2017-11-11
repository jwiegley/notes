Require Import Equations.Equations.
Require Import Vector.
From Equations Require Import Fin.

Inductive vector (A : Type) : nat -> Type :=
| nil : vector A 0
| cons (a : A) n (v : vector A n) : vector A (S n).

Arguments nil [A].
Arguments cons [A] a [n] v.

Inductive fin : nat -> Set :=
| fz : forall n, fin (S n)
| fs : forall n, fin n -> fin (S n).

Equations nth {A n} (v : vector A n) (f : fin n) : A :=
  nth (cons x _ _)    (fz n)    := x;
  nth (cons _ ?(n) v) (fs n f ) := nth v f .
