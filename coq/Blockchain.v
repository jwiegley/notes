Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.

Generalizable All Variables.
Set Transparent Obligations.

Section Blockchain.

Variable Ident : Type.
Variable Start : Ident.
Variable Block : Ident → Type.

Import ListNotations.

Inductive Chain : list Ident → Type :=
  | Genesis : Chain [Start]
  | Grow `(b : Block i) xs : ~ In i xs → Chain xs → Chain (i::xs).

Declare Instance Ident_UIP : Classes.UIP Ident.
Declare Instance Ident_EqDec : EqDec Ident.
Derive Signature NoConfusion for Chain.

Fail Fixpoint append `(x : Chain i) `(y : Chain j) : Chain i :=
  match x with
  | Genesis => y                (* error! j != Start *)
  | Grow b H c => Grow b H (append c y)
  end.

#[local]
Program Instance Blockchain : Category := {
  obj     := list Ident;
  hom     := λ x y, Chain x → Chain y;
  homset  := λ _ _, {| equiv f g := ∀ c, f c = g c |};
  id      := λ _ b, b;
  compose := λ _ _ _ f g b, f (g b);
}.
Next Obligation.
  equivalence.
  congruence.
Qed.
Next Obligation.
  proper.
  now rewrite H0, H.
Qed.

Lemma Chain_Genesis_irrelevant (x y : Chain [Start]) : x = y.
Proof.
  dependent elimination x.
  - dependent elimination y; auto.
    inv c.
  - inv c.
Qed.

#[local]
Program Instance Blockchain_Terminal : @Terminal Blockchain := {
  terminal_obj := [Start]
}.
Next Obligation.
  exact Genesis.
Defined.
Next Obligation.
  apply Chain_Genesis_irrelevant.
Qed.

(*
#[local]
Program Instance Blocks@{o h p} : Category@{o h p} := {
  obj     := Ident;
  hom     := tlist Block;
  homset  := λ _ _, {| equiv f g := f = g |};
  id      := λ _, tnil;
  compose := λ _ _ _ f g, g +++ f;
}.
Next Obligation. now apply tlist_app_tnil_r. Qed.
Next Obligation. now apply tlist_app_assoc. Qed.
Next Obligation. now symmetry; apply tlist_app_assoc. Qed.

#[local]
Program Instance Forget_Blockchain : Blockchain ⟶ Blocks := {
  fobj := λ x, x;
  fmap := λ x y f, _;
}.
Next Obligation.
  destruct (eq_dec x Start); subst.
  - specialize (f Genesis).
    generalize dependent y.
    induction 1; intros.
    + exact tnil.
    + admit.
  - admit.
Admitted.
*)

Import ListNotations.

#[local]
Program Instance OnlyBlocks@{o h p} : Category@{o h p} := {
  obj     := ();
  hom     := λ _ _, list (∃ i, Block i);
  homset  := λ _ _, {| equiv f g := f = g |};
  id      := λ _, nil;
  compose := λ _ _ _ f g, g ++ f;
}.
Next Obligation. now apply app_nil_r. Qed.
Next Obligation. now symmetry; apply app_assoc. Qed.
Next Obligation. now apply app_assoc. Qed.
