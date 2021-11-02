Require Import Coq.Vectors.Fin.
Require Import Coq.Program.Equality.

(** This file largely based on James Wilcox's article, "Reasoning about
    Cardinalities of Sums and Products":

    https://jamesrwilcox.com/more-cardinality.html *)

Class Isomorphism (x y : Type) : Type := {
  to   : x -> y;
  from : y -> x;

  iso_to_from : forall z, to (from z) = z;
  iso_from_to : forall z, from (to z) = z
}.

Theorem fin_0 : Isomorphism (Fin.t 0) False.
Proof.
  unshelve econstructor; intros.
  - inversion H.
  - contradiction.
  - contradiction.
  - inversion z.
Qed.

Theorem fin_1 : Isomorphism (Fin.t 1) unit.
Proof.
  unshelve econstructor; intros.
  - constructor.
  - constructor.
  - destruct z; reflexivity.
  - dependent destruction z; auto.
    inversion z.
Qed.

Definition fin_case n x :
  forall (P : Fin.t (S n) -> Type),
    P F1 ->
    (forall y, P (FS y)) ->
    P x :=
  match x as x0 in Fin.t n0
     return
       forall P,
         match n0 as n0' return (t n0' -> (t n0' -> Type) -> Type) with
           | 0 => fun _ _ => False
           | S m => fun x P => P F1 -> (forall x0, P (FS x0)) -> P x
         end x0 P
  with
    | F1 => fun _ H1 _ => H1
    | FS _ => fun _ _ HS => HS _
  end.

Ltac fin_dep_destruct v :=
  pattern v; apply fin_case; clear v; intros.

Fixpoint fin_of_sum_to_sum_of_fin {n m} {struct n} :
     Fin.t (n + m) -> Fin.t n + Fin.t m :=
  match n as n' return Fin.t (n' + m) -> Fin.t n' + Fin.t m with
    | 0 => fun x : t m => inr x
    | S n' => fun x : t (S (n' + m)) =>
                fin_case _ x _
                         (inl F1)
                         (fun x' : t (n' + m) =>
                            match fin_of_sum_to_sum_of_fin x' with
                              | inl a => inl (FS a)
                              | inr b => inr b
                            end)
  end.

Lemma fin_of_sum_to_sum_of_fin_L :
  forall m (x : Fin.t m) n,
    fin_of_sum_to_sum_of_fin (L n x) = inl x.
Proof.
  induction m; intros; simpl in *.
  - inversion x.
  - fin_dep_destruct x.
    + auto.
    + simpl.
      now rewrite IHm.
Qed.

Lemma L_fin_of_sum_to_sum_of_fin :
  forall n m (x : Fin.t (n + m)) t,
    fin_of_sum_to_sum_of_fin x = inl t ->
    L m t = x.
Proof.
  induction n; intros.
  - inversion t.
  - simpl in *.
    revert H.
    fin_dep_destruct x.
    + now inversion H.
    + simpl in *.
      destruct (fin_of_sum_to_sum_of_fin y) eqn:Heqe.
      * inversion H; subst; clear H.
        simpl.
        f_equal.
        now apply IHn.
      * discriminate.
Qed.

Lemma fin_of_sum_to_sum_of_fin_R :
  forall n m (x : Fin.t m),
    fin_of_sum_to_sum_of_fin (R n x) = inr x.
Proof.
  induction n; intros; simpl.
  - auto.
  - now rewrite IHn.
Qed.

Lemma R_fin_of_sum_to_sum_of_fin :
  forall n m (x : Fin.t (n + m)) t,
    fin_of_sum_to_sum_of_fin x = inr t ->
    R n t = x.
Proof.
  induction n; intros; simpl in *.
  - congruence.
  - revert H.
    fin_dep_destruct x.
    + discriminate.
    + simpl in *.
      destruct (fin_of_sum_to_sum_of_fin y) eqn:Heqe.
      * discriminate.
      * f_equal.
        inversion H; subst.
        now apply IHn.
Qed.

Theorem fin_plus n m : Isomorphism (Fin.t n + Fin.t m) (Fin.t (n + m)).
Proof.
  unshelve econstructor; intros.
  - inversion H.
    + now apply L.
    + now apply R.
  - now apply fin_of_sum_to_sum_of_fin.
  - simpl.
    destruct (fin_of_sum_to_sum_of_fin z) eqn:Heqe.
    + now apply L_fin_of_sum_to_sum_of_fin.
    + now apply R_fin_of_sum_to_sum_of_fin.
  - simpl.
    destruct z.
    + apply fin_of_sum_to_sum_of_fin_L.
    + apply fin_of_sum_to_sum_of_fin_R.
Qed.

Fixpoint prod_of_fin_to_fin_of_prod {n m} {struct n} :
      Fin.t n ->  Fin.t m -> Fin.t (n * m) :=
  match n as n' return Fin.t n' -> Fin.t m -> Fin.t (n' * m) with
    | 0 => fun x _ => case0 _ x
    | S n'' =>
      fun x y =>
        fin_case _ x _
                 (L _ y)
                 (fun x' => R _ (prod_of_fin_to_fin_of_prod x' y))
  end.

Fixpoint fin_of_prod_to_prod_of_fin {n m} {struct n} :
      Fin.t (n * m) -> Fin.t n * Fin.t m :=
  match n as n' return Fin.t (n' * m) -> Fin.t n' * Fin.t m with
    | 0 => fun x => case0 _ x
    | S n' =>
      fun x =>
        match fin_of_sum_to_sum_of_fin x with
          | inl a => (F1, a)
          | inr b => let (x,y) := fin_of_prod_to_prod_of_fin b
                     in (FS x, y)
        end
  end.

Lemma fin_prod_fin_inverse :
  forall n m x a b,
    @fin_of_prod_to_prod_of_fin n m x = (a,b) ->
    prod_of_fin_to_fin_of_prod a b = x.
Proof.
  induction n; intros.
  - inversion a.
  - simpl in *.
    fold mult in *.
    destruct (fin_of_sum_to_sum_of_fin x) eqn:Heqe.
    + inversion H; subst; clear H.
      simpl.
      auto using L_fin_of_sum_to_sum_of_fin.
    + destruct (fin_of_prod_to_prod_of_fin t) eqn:Heqe2.
      inversion H; subst; clear H.
      simpl.
      unshelve erewrite IHn; eauto.
      auto using R_fin_of_sum_to_sum_of_fin.
Qed.

Lemma prod_fin_prod_inverse :
  forall n m a b,
    @fin_of_prod_to_prod_of_fin n m (prod_of_fin_to_fin_of_prod a b) = (a,b).
Proof.
  induction n; intros.
  - inversion a.
  - fin_dep_destruct a; simpl.
    + rewrite fin_of_sum_to_sum_of_fin_L in *.
      auto.
    + rewrite fin_of_sum_to_sum_of_fin_R in *.
      rewrite IHn.
      auto.
Qed.

Theorem fin_mult n m : Isomorphism (Fin.t n * Fin.t m) (Fin.t (n * m)).
Proof.
  unshelve econstructor; intros.
  - destruct H.
    now apply prod_of_fin_to_fin_of_prod.
  - now apply fin_of_prod_to_prod_of_fin.
  - simpl.
    pose proof (fin_prod_fin_inverse _ _ z).
    destruct (fin_of_prod_to_prod_of_fin z); simpl in *.
    now apply H.
  - simpl.
    destruct z.
    apply prod_fin_prod_inverse.
Qed.

Theorem fin_exp n m : Isomorphism (Fin.t m -> Fin.t n) (Fin.t (Nat.pow n m)).
Proof.
  unshelve econstructor; intros.
  - generalize dependent n.
    induction m; simpl; intros.
    + exact Fin.F1.
    + rewrite <- PeanoNat.Nat.pow_succ_r'.
  - admit.
  - admit.
  - admit.
Admitted.
