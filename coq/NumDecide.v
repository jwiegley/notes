Set Warnings "-notation-overridden".

Require Import Coq.ZArith.ZArith.
Require Import Coq.FSets.FMaps.
Require Import Coq.Program.Program.

Open Scope Z_scope.

Generalizable All Variables.
Set Transparent Obligations.

(**************************************************************************
 * Data type for representing partial results, taken from Chlipala's CPDT
 *)

Inductive partial (P : Prop) : Set :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

(**************************************************************************
 * A term language for theorems involving FMaps
 *)

Record environment := {
  vars : positive -> Z
}.

Inductive term :=
  | Var   : positive -> term
  | Value : Z -> term.

Definition term_beq (x y : term) : bool :=
  match x, y with
  | Var x,   Var y   => (x =? y)%positive
  | Value x, Value y => (x =? y)%Z
  | _, _ => false
  end.

Program Definition term_eq_dec (x y : term) : {x = y} + {x <> y} :=
  match x, y with
  | Var x,   Var y   => if Pos.eq_dec x y then left _ else right _
  | Value x, Value y => if Z.eq_dec   x y then left _ else right _
  | _, _ => right _
  end.
Next Obligation.
  intuition; subst.
  destruct y.
    specialize (H0 p p); intuition.
  specialize (H z z); intuition.
Defined.
Next Obligation.
  split; unfold not; intros;
  destruct H1; discriminate.
Defined.
Next Obligation.
  split; unfold not; intros;
  destruct H1; discriminate.
Defined.

Definition subst_term (x v v' : term) : term :=
  if term_beq x v then v' else x.

Fixpoint subst_all_term (x : term) (xs : list (term * term)) : term :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_term (subst_term x v v') xs
  end.

Definition term_denote env (x : term) : Z :=
  match x with
  | Var n => vars env n
  | Value n => n
  end.

Inductive expr :=
  | Ref : term -> expr
  | Mul : expr -> expr -> expr
  | Add : expr -> expr -> expr.

Fixpoint subst_expr (t : expr) (v v' : term) : expr :=
  match t with
  | Ref x   => Ref (subst_term x v v')
  | Mul x y => Mul (subst_expr x v v') (subst_expr y v v')
  | Add x y => Add (subst_expr x v v') (subst_expr y v v')
  end.

Fixpoint subst_all_expr (x : expr) (xs : list (term * term)) : expr :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_expr (subst_expr x v v') xs
  end.

Lemma subst_all_expr_Ref defs : forall v,
  subst_all_expr (Ref v) defs = Ref (subst_all_term v defs).
Proof.
  induction defs; simpl; auto.
  destruct a; auto.
Qed.

Lemma subst_all_expr_Mul defs : forall x y,
  subst_all_expr (Mul x y) defs =
  Mul (subst_all_expr x defs) (subst_all_expr y defs).
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_all_expr_Add defs : forall x y,
  subst_all_expr (Add x y) defs =
  Add (subst_all_expr x defs) (subst_all_expr y defs).
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Fixpoint expr_denote env (m : expr) : Z :=
  match m with
  | Ref v => term_denote env v
  | Mul x y => (expr_denote env x * expr_denote env y)%Z
  | Add x y => (expr_denote env x + expr_denote env y)%Z
  end.

Inductive formula :=
  | Top    : formula
  | Bottom : formula
  | Equal  : expr -> expr -> formula
  | Impl   : formula -> formula -> formula.

Fixpoint subst_formula (t : formula) (v v' : term) : formula :=
  match t with
  | Top => Top
  | Bottom => Bottom
  | Equal x y => Equal (subst_expr x v v') (subst_expr y v v')
  | Impl p q => Impl (subst_formula p v v') (subst_formula q v v')
  end.

Fixpoint subst_all_formula (x : formula) (xs : list (term * term)) : formula :=
  match xs with
  | nil => x
  | cons (v, v') xs =>
    subst_all_formula (subst_formula x v v') xs
  end.

Lemma subst_all_formula_Top defs :
  subst_all_formula Top defs = Top.
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_all_formula_Bottom defs :
  subst_all_formula Bottom defs = Bottom.
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_all_formula_Equal defs : forall x y,
  subst_all_formula (Equal x y) defs =
  Equal (subst_all_expr x defs) (subst_all_expr y defs).
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Lemma subst_all_formula_Impl defs : forall p q,
  subst_all_formula (Impl p q) defs =
  Impl (subst_all_formula p defs) (subst_all_formula q defs).
Proof.
  induction defs; simpl; intros; auto.
  destruct a.
  rewrite IHdefs; reflexivity.
Qed.

Fixpoint formula_denote env (t : formula) : Prop :=
  match t with
  | Top       => True
  | Bottom    => False
  | Equal x y => expr_denote env x = expr_denote env y
  | Impl p q  => formula_denote env p -> formula_denote env q
  end.

(**************************************************************************
 * Compute structural size of formulas, for well-founded recursion
 *)

Fixpoint expr_size (t : expr) : nat :=
  match t with
  | Ref _ => 1%nat
  | Mul x y => 1%nat + expr_size x + expr_size y
  | Add x y => 1%nat + expr_size x + expr_size y
  end.

Fixpoint formula_size (t : formula) : nat :=
  match t with
  | Top => 1%nat
  | Bottom => 1%nat
  | Equal x y => 1%nat + expr_size x + expr_size y
  | Impl p q => formula_size p + formula_size q
  end.

Lemma all_formulas_have_size t : (0 < formula_size t)%nat.
Proof. induction t; simpl; omega. Qed.

Lemma expr_size_subst_all_expr defs m :
  expr_size (subst_all_expr m defs) = expr_size m.
Proof.
  induction m; simpl.
  - rewrite subst_all_expr_Ref; simpl; auto.
  - rewrite subst_all_expr_Mul; simpl; auto.
  - rewrite subst_all_expr_Add; simpl; auto.
Qed.

Lemma formula_size_subst_all_formula defs q :
  formula_size (subst_all_formula q defs) = formula_size q.
Proof.
  induction q; simpl.
  - rewrite subst_all_formula_Top; simpl; auto.
  - rewrite subst_all_formula_Bottom; simpl; auto.
  - rewrite subst_all_formula_Equal; simpl; auto.
    rewrite !expr_size_subst_all_expr; auto.
  - rewrite subst_all_formula_Impl; simpl; auto.
Qed.

(**************************************************************************
 * Substitution of variables throughout a formula
 *)

Definition substitution (x y : term) : option (term * term) :=
  match x, y with
  | Var n, Var m => if Pos.eq_dec n m then None else Some (x, y)
  | Var _, _  => Some (x, y)
  | _ , Var _ => Some (y, x)
  | _, _ => None
  end.

Fixpoint substitutions (xs : list (term * term)) : list (term * term) :=
  match xs with
  | nil => nil
  | cons (x, y) xs =>
    match substitution x y with
    | Some p => cons p (substitutions xs)
    | None => substitutions xs
    end
  end.

Lemma term_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
  -> term_denote env (subst_all_term t (substitutions xs)) =
     term_denote env t.
Proof.
  generalize dependent t.
  induction xs; simpl; intros; auto.
  inversion H; subst; clear H.
  destruct a as [x y]; simpl in *.
  destruct t; simpl; intros.
  - destruct x, y; simpl in *; intros; auto.
    + destruct (Pos.eq_dec p0 p1); simpl; auto.
        rewrite IHxs; auto.
      unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        rewrite IHxs; auto.
      apply Pos.eqb_neq in n0; rewrite n0; simpl; auto.
      apply IHxs; auto.
    + unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        apply IHxs; auto.
      apply Pos.eqb_neq in n; rewrite n; simpl; auto.
      apply IHxs; auto.
    + unfold subst_term; simpl.
      destruct (Pos.eq_dec p p0); subst.
        rewrite Pos.eqb_refl; simpl; auto.
        apply IHxs; auto.
      apply Pos.eqb_neq in n; rewrite n; simpl; auto.
      apply IHxs; auto.
    + apply IHxs; auto.
  - destruct x, y; simpl in *; intros; try apply IHxs; auto.
    destruct (Pos.eq_dec p p0); simpl; apply IHxs; auto.
Qed.

Lemma expr_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> expr_denote env (subst_all_expr t (substitutions xs)) =
       expr_denote env t.
Proof.
  induction t; simpl; intros.
  - rewrite subst_all_expr_Ref; simpl; auto.
    rewrite !term_substitution_eq; auto.
  - rewrite subst_all_expr_Mul; simpl; intros.
    rewrite IHt1, IHt2; auto.
  - rewrite subst_all_expr_Add; simpl; intros.
    rewrite IHt1, IHt2; auto.
Qed.

Lemma formula_substitution_eq env t xs :
  Forall (fun p => term_denote env (fst p) = term_denote env (snd p)) xs
    -> formula_denote env (subst_all_formula t (substitutions xs)) =
       formula_denote env t.
Proof.
  induction t; simpl; intros.
  - rewrite subst_all_formula_Top; simpl; auto.
  - rewrite subst_all_formula_Bottom; simpl; auto.
  - rewrite subst_all_formula_Equal; simpl; intros.
    rewrite !expr_substitution_eq; auto.
  - rewrite subst_all_formula_Impl; simpl; intros.
    intuition.
    rewrite H0, H1; auto.
Qed.

(**************************************************************************
 * Computational decision procedure for map membership
 *)

Program Definition formula_forward (t : formula) env (hyp : formula)
        (cont : forall env' defs, [formula_denote env' (subst_all_formula t defs)]) :
  [formula_denote env hyp -> formula_denote env t] :=
  match hyp with
  | Top => Reduce (cont env nil)
  | Bottom => Yes
  | Equal x y => No             (* Benoit: TODO *)
  | Impl _ _ => Reduce (cont env nil)
  end.
Next Obligation.
  contradiction.
Defined.

(* Benoit: TODO: This should be changed to fit your problem. *)
Definition decision (env : environment) (m n : expr) : bool :=
  Z.eqb (expr_denote env m) (expr_denote env n).

Program Fixpoint formula_backward (t : formula) env {measure (formula_size t)} :
  [formula_denote env t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equal x y => match decision env x y with
                 | true => Yes
                 | false => No
                 end
  | Impl p q =>
    formula_forward q env p
      (fun env' defs' => formula_backward (subst_all_formula q defs') env')
  end.
Next Obligation.
  unfold decision in Heq_anonymous.
  symmetry in Heq_anonymous.
  apply Z.eqb_eq in Heq_anonymous.
  assumption.
Defined.
Next Obligation.
  rewrite formula_size_subst_all_formula; simpl.
  apply Nat.lt_add_pos_l, all_formulas_have_size.
Defined.

Definition formula_tauto : forall env t, [formula_denote env t].
Proof.
  intros; refine (Reduce (formula_backward t env)); auto.
Defined.

Lemma formula_sound env t :
  (if formula_tauto env t then True else False) -> formula_denote env t.
Proof.
  unfold formula_tauto; destruct t, (formula_backward _ env); tauto.
Qed.

(**************************************************************************
 * Environment management tactics
 *)

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    lazymatch xs' with
    | tt => constr:(fun _ : positive => 0%Z)
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop (1%positive) xs.

Ltac allVar xs e :=
  match e with
  | Z0 => xs
  | Zpos _ => xs
  | Zneg _ => xs
  | _ => addToList e xs
  end.

Ltac allVars xs e :=
  match e with
  | ?X * ?Y =>
    let xs := allVar xs X in
    allVar xs Y
  | ?X + ?Y =>
    let xs := allVar xs X in
    allVar xs Y
  | ?P = ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | ?P -> ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | ?X => allVar xs X           (* Benoit: TODO: This may be too open *)
  | _ => xs
  end.

(**************************************************************************
 * Reflection tactics
 *)

Ltac reifyValue env t :=
  match t with
  | Z0 => constr:(Value Z0)
  | Zneg ?X =>
    constr:(Value (Zneg X))
  | Zpos ?X =>
    constr:(Value (Zpos X))
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  end.

Ltac reifyExpr env t :=
  match t with
  | ?X * ?Y =>
    let x := reifyExpr env X in
    let y := reifyExpr env Y in
    constr:(Mul x y)
  | ?X + ?Y =>
    let x := reifyExpr env X in
    let y := reifyExpr env Y in
    constr:(Add x y)
  | ?X =>
    let x := reifyValue env X in
    constr:(Ref x)
  end.

Ltac reifyTerm env t :=
  match t with
  | True => constr:(Top)
  | False => constr:(Bottom)
  | ?X = ?Y =>
    let x := reifyExpr env X in
    let y := reifyExpr env Y in
    constr:(Equal x y)
  | ?P -> ?Q =>
    let p := reifyTerm env P in
    let q := reifyTerm env Q in
    constr:(Impl p q)
  end.

Ltac gather_vars :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    pose xs
  end.

Ltac reify' :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1
  end.

Ltac reify :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    change (formula_denote {| vars := env |} r1)
  end.

(**************************************************************************
 * User interface tactics
 *)

Ltac maths := reify; apply formula_sound; vm_compute; auto.

Goal 2 * 3 = 3 * 2.
  maths.
Qed.
