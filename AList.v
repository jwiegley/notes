Require Import Coq.Lists.List.
Require Export Coq.Classes.CEquivalence.
Require Export Coq.Bool.Bool.

Open Scope lazy_bool_scope.

Require Import Equations.Equations.
Unset Equations WithK.

Notation "( x ; y )" := (existT _ x y) (at level 0).

Inductive alist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | anil : forall i : A, alist B i i
  | acons : forall (i j k : A) (x : B i j) (xs : alist B j k), alist B i k.

Derive Signature Subterm for alist.

Arguments anil {A B i}.
Arguments acons {A B i j k} x xs.

Infix ":::" := acons (at level 42, right associativity).

Section AList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Fixpoint alist_length {i j} (xs : alist B i j) : nat :=
  match xs with
  | anil => 0
  | acons x xs => 1 + alist_length xs
  end.

Equations alist_app {i j k} (xs : alist B i j) (ys : alist B j k) :
  alist B i k :=
  alist_app anil ys := ys;
  alist_app xs anil := xs;
  alist_app (acons x xs) ys := x ::: alist_app xs ys.

Equations alist_uncons {i j} (xs : alist B i j) :
  option { z : A & B i z * alist B z j }%type :=
  alist_uncons anil := None;
  alist_uncons (acons x xs) := Some (_; (x, xs)).

Equations alist_map {i j A' C} {f : A -> A'}
          (g : forall i j : A, B i j -> C (f i) (f j))
          (xs : alist B i j) : alist C (f i) (f j) :=
  alist_map _ anil := anil;
  alist_map g (acons x xs) := g _ _ x ::: alist_map g xs.

Equations alist_head {i j} (xs : alist B i j) :
  option { z : A & B i z }%type :=
  alist_head anil := None;
  alist_head (acons x xs) := Some (_; x).

Equations alist_tail {i j} (xs : alist B i j) :
  option { z : A & alist B z j }%type :=
  alist_tail anil := None;
  alist_tail (acons x xs) := Some (_; xs).

Equations alist_init {i j} (xs : alist B i j) :
  option { z : A & alist B i z }%type :=
  alist_init anil := None;
  alist_init (acons x xs) <= alist_init xs => {
    | None => Some (_; anil);
    | Some (existT _ ys) => Some (_; (x ::: ys))
  }.

Equations alist_last {i j} (xs : alist B i j) :
  option { z : A & B z j }%type :=
  alist_last anil := None;
  alist_last (acons x xs) <= xs => {
    | anil => Some (_; x);
    | acons y ys => alist_last ys
  }.

Import EqNotations.

(* Returns true if [xs] is a sublist of [ys] *)
Equations alist_equiv_sublist
          (A_eq_dec : forall x y : A, { x = y } + { x <> y })
          (B_equivb : forall (i j : A) (x y : B i j), bool)
          {i j} (xs : alist B i j)
          {k l} (ys : alist B k l) : bool :=
  alist_equiv_sublist _ _ anil _ := true;
  alist_equiv_sublist _ _ _ anil := false;
  alist_equiv_sublist eq_dec equivb (acons i m j x xs) (acons k n l y ys)
    <= (eq_dec i k, eq_dec m n) => {
      | pair (left H1) (left H2) =>
        (equivb _ _ x (rew <- [fun y => B i y] H2 in
                       rew <- [fun x => B x n] H1 in y)
           &&& alist_equiv_sublist eq_dec equivb xs ys)
          ||| alist_equiv_sublist eq_dec equivb (x ::: xs) ys;
      | _ => alist_equiv_sublist eq_dec equivb (x ::: xs) ys
    }.
Next Obligation.
  (* Why isn't this obvious? *)
Admitted.

End AList.

Section AListProofs.

Context {A : Type}.
Context {B : A -> A -> Type}.

Lemma alist_app_anil_left {i j} (xs : alist B i j) :
  alist_app anil xs = xs.
Proof. now destruct xs. Qed.

Lemma alist_app_anil_right {i j} (xs : alist B i j) :
  alist_app xs anil = xs.
Proof. now destruct xs. Qed.

Lemma alist_app_assoc {i j k l}
      (xs : alist B i j) (ys : alist B j k) (zs : alist B k l) :
  alist_app (alist_app xs ys) zs = alist_app xs (alist_app ys zs).
Proof.
  induction xs, ys, zs; auto; simpl.
  now rewrite IHxs.
Qed.

End AListProofs.

Section AListProofsInj.

(* Dependending on the choice of A, this can be either
      Eqdep.EqdepTheory.inj_pair2  (incurs axiom)
   or Eqdep_dec.inj_pair2_eq_dec   (when A is decidable)
*)
Hypothesis inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    (p; x) = (p; y) -> x = y.

Context {A : Type}.
Context {B : A -> A -> Type}.

Lemma alist_cons_uncons
      {i m j} (xs : alist B i j) (y : B i m) ys :
  alist_uncons xs = Some (_; (y, ys)) -> xs = acons y ys.
Proof.
  destruct xs; simpl; intros.
    inversion H.
  inversion H; subst; clear H.
  apply inj_pair2 in H2; auto.
  apply inj_pair2 in H3; auto.
  now subst.
Qed.

End AListProofsInj.

Reserved Infix "<+>" (at level 42, right associativity).

Class IMonoid {A : Type} (B : A -> A -> Type) := {
  imempty {i : A} : B i i;
  imappend {i j k : A} : B i j -> B j k -> B i k
    where "x <+> y" := (imappend x y);

  imempty_left {i j} {x : B i j} : imempty <+> x = x;
  imempty_right {i j} {x : B i j} : x <+> imempty = x;
  imappend_assoc {i j k l} {x : B i j} {y : B j k} {z : B k l} :
    (x <+> y) <+> z = x <+> (y <+> z)
}.

Infix "<+>" := imappend (at level 42, right associativity).

Instance alist_IMonoid {A} {B : A -> A -> Type} : IMonoid (alist B) := {
  imempty := @anil A B;
  imappend := @alist_app A B;
  imempty_left := @alist_app_anil_left A B;
  imempty_right := @alist_app_anil_right A B;
  imappend_assoc := @alist_app_assoc A B
}.
