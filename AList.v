Require Import Coq.Lists.List.
Require Import Coq.Classes.CEquivalence.
Require Import Coq.Bool.Bool.

Open Scope lazy_bool_scope.

Require Import Equations.Equations.
Unset Equations WithK.

Notation "( x ; y )" := (existT _ x y) (at level 0).

Inductive alist {A : Type} (B : A -> A -> Type) : A -> A -> Type :=
  | anil : forall i : A, alist B i i
  | acons : forall (i j k : A) (x : B i j) (xs : alist B j k), alist B i k.

Derive Signature Subterm for alist.

Arguments anil {A B i}.
Arguments acons {A B i} j {k} x xs.

Notation "x ::: xs" := (acons _ x xs) (at level 42, right associativity).

Section AList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Fixpoint alist_length {i j} (xs : alist B i j) : nat :=
  match xs with
  | anil => 0
  | acons x _ xs => 1 + alist_length xs
  end.

(* The Fixpoint version does not work, as might be expected, but fails with
   this rather confusing error:

     Error: Illegal application:
     The term "@eq" of type "forall A : Type, A -> A -> Prop"
     cannot be applied to the terms
      "A" : "Type"
      "k'" : "A"
      "ys0" : "alist B j'0 k'"
     The 3rd term has type "alist B j'0 k'" which should be coercible to "A".

Program Fixpoint alist_app {i j k} (xs : alist B i j) (ys : alist B j k) :
  alist B i k :=
  match xs, ys with
  | anil, ys => ys
  | xs, anil => xs
  | acons x xs, ys => x ::: alist_app xs ys
  end.
*)

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
          {j k} (xs : alist B j k)
          {i l} (ys : alist B i l) : bool :=
  alist_equiv_sublist eq_dec equivb (anil j) (anil i)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => false
    };
  alist_equiv_sublist eq_dec equivb (anil j) (acons i _ _ y ys)
    <= eq_dec j i => {
      | left _ => true;
      | right _ => alist_equiv_sublist eq_dec equivb anil ys
    };
  alist_equiv_sublist _ _ _ anil := false;
  alist_equiv_sublist eq_dec equivb (acons j m _ x xs) (acons i o _ y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2) =>
        (equivb _ _ x (rew <- [fun y => B _ y] H2 in
                       rew <- [fun x => B x _] H1 in y)
           &&& alist_equiv_sublist eq_dec equivb xs ys)
          ||| alist_equiv_sublist eq_dec equivb (x ::: xs) ys;
      | _ => alist_equiv_sublist eq_dec equivb (x ::: xs) ys
    }.

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
  alist_uncons xs = Some (_; (y, ys)) -> xs = y ::: ys.
Proof.
  destruct xs; simpl; intros.
    inversion H.
  inversion H; subst; clear H.
  apply inj_pair2 in H2; auto.
  apply inj_pair2 in H3; auto.
  now subst.
Qed.

End AListProofsInj.

Section WList.

Context {A : Type}.
Context {B : A -> A -> Type}.

Inductive wlist : A -> forall j k l, alist B j k -> Type :=
  | segments : forall (i j k l : A) (xs : alist B i j) ys
                      (zs : alist B k l), wlist i j k l ys.

Arguments segments {i j k l} xs ys zs.

Import EqNotations.

Equations alist_find_wlist
          (A_eq_dec : forall x y : A, { x = y } + { x <> y })
          (B_equivb : forall (i j : A) (x y : B i j), bool)
          {j k} (xs : alist B j k)
          {i l} (ys : alist B i l) : option (wlist i j k l xs) :=
  alist_find_wlist eq_dec equivb (anil j) (anil i)
    <= eq_dec j i => {
      | left H => Some (rew <- [fun x => wlist _ x x _ anil] H
                          in segments anil anil anil);
      | _ => None
    };
  alist_find_wlist eq_dec equivb (anil j) (acons k n l y ys)
    <= eq_dec j k => {
      | left H =>
        Some (rew <- [fun x => wlist _ x x _ anil] H
                in segments anil anil (y ::: ys));
      | _ <= alist_find_wlist eq_dec equivb anil ys => {
        | None => None;
        | Some (segments ys _ zs) =>
          Some (segments (y ::: ys) anil zs)
      }
    };
  alist_find_wlist _ _ _ anil := None;
  alist_find_wlist eq_dec equivb (acons j m k x xs) (acons i o l y ys)
    <= (eq_dec j i, eq_dec m o) => {
      | pair (left H1) (left H2)
        <= equivb _ _ x (rew <- [fun y => B _ y] H2 in
                         rew <- [fun x => B x _] H1 in y) => {
          | true <= alist_find_wlist eq_dec equivb xs ys => {
              | Some (segments ys ws zs) =>
                Some (rew [fun a => wlist a j wildcard1 wildcard2 (x ::: ws)] H1
                        in segments anil (x ::: ws) zs);
              | None <= alist_find_wlist eq_dec equivb (x ::: xs) ys => {
                  | None => None;
                  | Some (segments ys _ zs) =>
                    Some (segments (y ::: ys) (x ::: xs) zs)
                }
            };
          | false <= alist_find_wlist eq_dec equivb (x ::: xs) ys => {
              | None => None;
              | Some (segments ys _ zs) =>
                Some (segments (y ::: ys) (x ::: xs) zs)
            }
        };
      | _  <= alist_find_wlist eq_dec equivb (x ::: xs) ys => {
          | None => None;
          | Some (segments ys _ zs) =>
            Some (segments (y ::: ys) (x ::: xs) zs)
        }
      }.

End WList.

Arguments segments {A B i j k l} xs ys zs.

Definition nat_triple := fun (_ _ : nat) => ((nat * nat) * nat)%type.

Definition my_list : alist nat_triple 0 4 :=
  acons 1 ((0, 1), 100)
        (acons 2 ((1, 2), 200)
               (acons 3 ((2, 3), 300)
                      (acons 4 ((3, 4), 400)
                             anil))).

Lemma nat_eq_dec (x y : nat) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Require Import Coq.Arith.EqNat.

Definition nat_equivb (x y : ((nat * nat) * nat)) : bool :=
  match x, y with
    (_, a), (_, b) => beq_nat a b
  end.

Example alist_find_wlist_nat_ex1 :
  @alist_find_wlist nat nat_triple nat_eq_dec (fun _ _ => nat_equivb)
                    1 3 (acons 2 ((1, 2), 200) (acons 3 ((2, 3), 300) anil))
                    0 4 my_list
    = Some (segments ((0, 1, 100) ::: anil)
                     ((1, 2, 200) ::: (2, 3, 300) ::: anil)
                     ((3, 4, 400) ::: anil)).
Proof. reflexivity. Qed.

Print Assumptions alist_find_wlist_nat_ex1.

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
