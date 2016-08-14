(* This is a basic PHOAS encoding for the Simply Typed Lambda Calculus,
   enriched with let bindings, booleans, and natural numbers. *)

Section AST.

Inductive type :=
  | Bool : type
  | Nat  : type
  | Func : type -> type -> type.

Variable var : type -> Type.

Infix "→" := Func (right associativity, at level 52) : Lambda_scope.

Open Scope Lambda_scope.

Inductive term : type -> Type :=
  (* The basic, simply-typed lambda calculus *)
  | TVar : forall t, var t -> term t
  | TAbs : forall dom cod, (var dom -> term cod) -> term (dom → cod)
  | TApp : forall dom cod, term (dom → cod) -> term dom -> term cod

  (* Extended with let, bool and nat *)
  | TLet : forall t1 t2, term t1 -> (var t1 -> term t2) -> term t2

  | TTrue : term Bool
  | TFalse : term Bool

  | TConst : nat -> term Nat
  | TNeg : term Nat -> term Nat

  | TPlus  : term Nat -> term Nat -> term Nat
  | TMinus : term Nat -> term Nat -> term Nat
  | TMult  : term Nat -> term Nat -> term Nat

  | TLt : term Nat -> term Nat -> term Bool
  | TLe : term Nat -> term Nat -> term Bool
  | TEq : term Nat -> term Nat -> term Bool
  | TGe : term Nat -> term Nat -> term Bool
  | TGt : term Nat -> term Nat -> term Bool

  | TAnd : term Bool -> term Bool -> term Bool
  | TOr  : term Bool -> term Bool -> term Bool
  | TNot : term Bool -> term Bool.

End AST.

Arguments TVar [var t] _.
Arguments TAbs [var dom cod] _.
Arguments TApp [var dom cod] _ _.

Arguments TLet [var t1 t2] _ _.

Arguments TTrue [var].
Arguments TFalse [var].

Arguments TConst [var] _.
Arguments TNeg [var] _.

Arguments TPlus [var] _ _.
Arguments TMinus [var] _ _.
Arguments TMult [var] _ _.

Arguments TLt [var] _ _.
Arguments TLe [var] _ _.
Arguments TEq [var] _ _.
Arguments TGe [var] _ _.
Arguments TGt [var] _ _.

Arguments TAnd [var] _ _.
Arguments TOr [var] _ _.
Arguments TNot [var] _.

Section Denotation.

Fixpoint typeDenote (t : type) : Type :=
  match t with
  | Bool         => bool
  | Nat          => nat
  | Func arg ret => typeDenote arg -> typeDenote ret
  end.

Require Import PeanoNat.

Open Scope bool_scope.

Fixpoint termDenote {t} (e : term typeDenote t) : typeDenote t :=
  match e with
  | TVar x     => x
  | TAbs f     => fun v => termDenote (f v)
  | TApp e1 e2 => termDenote e1 (termDenote e2)

  | TLet x f   => termDenote (f (termDenote x))

  | TTrue => true
  | TFalse => false

  | TConst x => x
  | TNeg x => 0 - termDenote x

  | TPlus x y => termDenote x + termDenote y
  | TMinus x y => termDenote x - termDenote y
  | TMult x y => termDenote x * termDenote y

  | TEq x y => termDenote x =? termDenote y
  | TLt x y => termDenote x <? termDenote y
  | TLe x y => ((termDenote x =? termDenote y) ||
                (termDenote x <? termDenote y))
  | TGe x y => ((termDenote x =? termDenote y) ||
                (negb (termDenote x <? termDenote y)))
  | TGt x y => ((negb (termDenote x =? termDenote y)) &&
                (negb (termDenote x <? termDenote y)))

  | TAnd x y => termDenote x && termDenote y
  | TOr x y => termDenote x || termDenote y
  | TNot x => negb (termDenote x)
  end.

End Denotation.

Bind Scope Lambda_scope with term.

Delimit Scope Lambda_scope with Lam.

Infix "→" := Func (right associativity, at level 52) : Lambda_scope.

Notation "^" := TVar (at level 49) : Lambda_scope.
Notation "\ x : t , e" := (TAbs (dom:=t) (fun x => e))
  (no associativity, at level 100, x at level 0) : Lambda_scope.
Infix "@" := TApp (left associativity, at level 50) : Lambda_scope.

Notation "'Let' x : t := e1 'in' e2" := (TLet (t1:=t) e1 (fun x => e2))
  (no associativity, at level 100, x at level 0) : Lambda_scope.

Notation "#" := TConst (at level 49) : Lambda_scope.

Notation "x + y"  := (TPlus x y) : Lambda_scope.
Notation "x - y"  := (TMinus x y) : Lambda_scope.
Notation "x * y"  := (TMult x y) : Lambda_scope.

Notation "x == y" := (TEq x y) (at level 99) : Lambda_scope.
Notation "x < y"  := (TLt x y) : Lambda_scope.
Notation "x <= y" := (TLe x y) : Lambda_scope.
Notation "x >= y" := (TGe x y) : Lambda_scope.
Notation "x > y"  := (TGt x y) : Lambda_scope.

Notation "x && y" := (TAnd x y) : Lambda_scope.
Notation "x || y" := (TOr x y) : Lambda_scope.
Notation "! x"    := (TNot x) (at level 50) : Lambda_scope.

Notation "[ e ]" := (fun _ => e) : Lambda_scope.

Definition Term t := forall v, term v t.

Definition eval {t} (e : Term t) : typeDenote t := termDenote (e typeDenote).

Compute (eval [#1 + #2 == #2 + #1])%Lam.
Compute (eval [(\x : Nat, #1 + ^x == #2 + #1) @ #2])%Lam.
Compute (eval [Let x : Nat := #2 in #1 + ^x == #2 + #1])%Lam.
