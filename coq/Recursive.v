Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrbool.
Require Import Ssreflect.eqtype.
Require Import Ssreflect.seq.
Require Import Ssreflect.ssrnat.

Inductive ExprF (d : (Type -> Type) -> Type -> Type)
                (c : Type -> Type) (e : Type) : Type :=
  | eLambda  (x:nat) (e':e)
  | eVar     (x:nat)
  | eAscribe (e':e)  (t:d c e)
  | ePlus    (e1:e) (e2:e).

Inductive DTypeF (c : Type -> Type) (e : Type) : Type :=
  | tArrow (x:nat) (t:e) (c':c e) (t':e)
  | tInt.

Inductive ConstraintF (e : Type) : Type :=
  | cEq (e1:e) (e2:e).

Definition Mu (f : Type -> Type) := forall a, (f a -> a) -> a.

Definition Constraint := Mu ConstraintF.
Definition DType      := Mu (DTypeF ConstraintF).
Definition Expr       := Mu (ExprF DTypeF ConstraintF).

Definition substInExpr (x:nat) (v:Expr) (e':Expr) : Expr := fun a phi =>
  e' a (fun e => match e return a with
    (* interesting cases *)
    | eLambda y e' =>
        if (x == y) then e' else phi e
    | eVar y =>
        if (x == y) then v _ phi else phi e

    (* boring cases *)
    | _ => phi e
    end).

Definition varNum (x:ExprF DTypeF ConstraintF nat) : nat :=
  match x with
  | eLambda _ e => e
  | eVar y => y
  | _ => 0
  end.

Compute (substInExpr 2 (fun a psi => psi (eVar _ _ _ 3))
                     (fun _ phi =>
                        phi (eLambda _ _ _ 1 (phi (eVar _ _ _ 2)))))
        nat varNum.

Compute (substInExpr 1 (fun a psi => psi (eVar _ _ _ 3))
                     (fun _ phi =>
                        phi (eLambda _ _ _ 1 (phi (eVar _ _ _ 2)))))
        nat varNum.
