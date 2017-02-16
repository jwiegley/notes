Require Import Fiat.ADT Fiat.ADTNotation.
Require Export Fiat.Computation.FixComp.

Import LeastFixedPointFun.

Instance refineFun_Reflexive fDom fCod : Reflexive (@refineFun fDom fCod).
Proof.
  intro x.
  induction fDom; simpl; intros.
    reflexivity.
  simpl in x.
  apply IHfDom.
Qed.

Add Parametric Morphism fDom fCod : (@refineFun fDom fCod)
  with signature
    ((@refineFun fDom fCod) --> (@refineFun fDom fCod) ++> impl)
    as refineFun_refineFun.
Proof.
  unfold impl; intros.
  induction fDom; simpl in *; intros.
    rewrite H, H1, H0.
    reflexivity.
  specialize (IHfDom (x t) (y t) (H t) (x0 t) (y0 t)).
  firstorder.
Qed.

Add Parametric Morphism fDom fCod : (@refineFun fDom fCod)
  with signature
    ((@refineFun fDom fCod) ==> Basics.flip (@refineFun fDom fCod)
       ==> Basics.flip impl)
    as refineFun_refineFun_flip.
Proof.
  unfold impl; intros.
  induction fDom; simpl in *; intros.
    rewrite H, H1; assumption.
  specialize (IHfDom (x t) (y t) (H t) (x0 t) (y0 t)).
  firstorder.
Qed.

Instance refineFun_Transitive fDom fCod : Transitive (@refineFun fDom fCod).
Proof.
  intros x y z H1 H2.
  rewrite H1.
  exact H2.
Qed.

Program Instance refineFun_PreOrder fDom fCod : PreOrder (@refineFun fDom fCod).

Definition refineFunEquiv
           {fDom : list Type}
           {fCod : Type}
           (old new : funType fDom fCod) :=
  refineFun old new /\ refineFun new old.

Add Parametric Morphism fDom fCod
: (@refineFun fDom fCod)
  with signature
  (@refineFunEquiv fDom fCod) --> (@refineFunEquiv fDom fCod) ++> impl
    as refineFun_refineFunEquiv.
Proof.
  unfold impl, refineFunEquiv; intros.
  intuition.
  rewrite H2, H1.
  assumption.
Qed.

Add Parametric Morphism fDom fCod
: (@refineFun fDom fCod)
    with signature
    (@refineFunEquiv fDom fCod --> @refineFunEquiv fDom fCod
        --> Basics.flip impl)
      as refineFun_refineFunEquiv'.
Proof.
  unfold impl, refineFunEquiv; intros.
  intuition.
  rewrite H3, H1.
  assumption.
Qed.

Program Instance refineFunEquiv_Equivalence fDom fCod :
  Equivalence (@refineFunEquiv fDom fCod).
Obligation 1.
  unfold refineFunEquiv.
  intro x.
  split; reflexivity.
Defined.
Obligation 2.
  unfold refineFunEquiv.
  intros x y H.
  intuition.
Qed.
Obligation 3.
  unfold refineFunEquiv.
  intros x y z H1 H2.
  intuition.
  transitivity y; trivial.
  transitivity y; trivial.
Qed.

(*
Corollary FixedPointP_is_refineFunEquiv
          {fDom : list Type}
          {fCod : Type}
          (fDef : funType fDom fCod -> funType fDom fCod)
          (fSet : funType fDom fCod) :
  FixedPointP fDef fSet = refineFunEquiv (fDef fSet) fSet.
Proof. reflexivity. Qed.
*)

Instance refineFun_refineFunEquiv_subrelation fDom fCod :
  subrelation (@refineFunEquiv fDom fCod) (@refineFun fDom fCod).
Proof. intros ? ? [? ?]; assumption. Qed.

(*
Add Parametric Morphism fDom fCod : (@FixedPointP fDom fCod)
  with signature
    ((@refineFunEquiv fDom fCod) ==> (@refineFunEquiv fDom fCod))
       ==> (@refineFunEquiv fDom fCod) ==> impl
    as refineFun_FixedPointP.
Proof.
  unfold respectful, FixedPointP, refineFunEquiv, impl; simpl; intros.
  specialize (H _ _ H0).
  intuition.
  - rewrite H3, H0; assumption.
  - rewrite H2 in H5.
    rewrite H5 in H4.
    assumption.
Qed.
*)

Lemma length_wf' : forall A len l,
  length l < len -> Acc (fun l1 l2 : list A => length l1 < length l2) l.
Proof.
  induction len; simpl; intros;
  constructor; intros.
    contradiction (NPeano.Nat.nlt_0_r _ H).
  apply IHlen.
  Require Import Omega.
  omega.
Qed.

Lemma length_wf : forall A,
  well_founded (fun l1 l2 : list A => length l1 < length l2).
Proof.
  red; intros; eapply length_wf'; eauto.
Qed.

Definition funType_to_methodType
      {rep : Type} {dom : list Type} {cod : Type} :
  funType (rep :: dom) (rep * cod) -> methodType rep dom (Some cod).
Proof.
  simpl; intro f.
  intro r'.
  specialize (f r'); clear r'.
  induction dom; simpl in *.
    exact f.
  intro r'.
  exact (IHdom (f r')).
Defined.

Definition methodType_to_funType
      {rep : Type} {dom : list Type} {cod : Type} :
  methodType rep dom (Some cod) -> funType (rep :: dom) (rep * cod).
Proof.
  simpl; intro f.
  intro r'.
  specialize (f r'); clear r'.
  induction dom; simpl in *.
    exact f.
  intro r'.
  exact (IHdom (f r')).
Defined.

Lemma methodType_to_funType_id
      {rep : Type} {dom : list Type} {cod : Type}
      (f : funType (rep :: dom) (rep * cod)) :
  methodType_to_funType (funType_to_methodType f) = f.
Proof.
  unfold methodType_to_funType, funType_to_methodType.
  extensionality r.
  induction dom; simpl in f;
  extensionality x; simpl.
    reflexivity.
  exact (IHdom (fun r => f r x)).
Qed.

Import EqNotations.

Require Import Fiat.Common.Frame.

Inductive hetero {A : Type} {B : A -> Type} : list A -> Type :=
  | hnil : hetero []
  | hcons x xs : hetero xs -> B x -> hetero (x :: xs).

Ltac under_fDom :=
  match goal with
  | [ fDom : list Type |- _ ] =>
    induction fDom; simpl in *;
    [| intros;
       repeat
         match goal with
         | [ f : ?OLDREP -> ?A -> funType ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : (OLDREP -> funType FDOM FCOD) -> _,
               x : A |- _ ] =>
             specialize (IHfDom (fun r => f r x));
             try exact IHfDom;
             try clear f
           end
         | [ f : ?OLDREP -> ?A -> methodType' ?OLDREP ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : (OLDREP -> methodType' OLDREP FDOM FCOD) -> _,
               x : A |- _ ] =>
             specialize (IHfDom (fun r => f r x));
             try exact IHfDom;
             try clear f
           end
         | [ f : ?A -> funType ?FDOM ?FCOD |- _ ] =>
           match goal with
             [ IHfDom : funType FDOM FCOD -> _,
               x : A |- _ ] =>
             specialize (IHfDom (f x));
             try exact IHfDom;
             try clear f
           end
         end ]
  end.

Definition funApply {fDom fCod} :
  funType fDom fCod -> hetero (B:=id) fDom -> Comp fCod.
Proof.
  intros.
  induction fDom; simpl in *.
    exact X.
  inversion X0.
  exact (IHfDom (X X2) X1).
Defined.

Definition cod_old_to_new {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType fDom (oldRep * fCod) -> funType fDom (newRep * fCod).
Proof.
  simpl; intros f.
  under_fDom.
  exact (p <- f;
         n <- { n : newRep | AbsR (fst p) n };
         ret (n, snd p)).
Defined.

Definition funType_join {fDom fCod} :
  Comp (funType fDom fCod) -> funType fDom fCod.
Proof.
  intros.
  induction fDom.
    exact (v <- X; v).
  intro x.
  exact (IHfDom (f <- X; ret (f x))).
Defined.

Definition dom_new_to_old {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop) :
  funType (newRep :: fDom) fCod -> funType (oldRep :: fDom) fCod.
Proof.
  simpl; intros f o.
  under_fDom.
  exact (n <- { n : newRep | AbsR o n };
         f n).
Defined.

Definition refineFun_invert
           {newRep oldRep fDom fCod}
           (AbsR : oldRep -> newRep -> Prop)
           (f : funType (oldRep :: fDom) (oldRep * fCod))
           (f' : funType (newRep :: fDom) (newRep * fCod)) :
  (forall (args : hetero fDom),
     pointwise_relation _ refine
                        (fun or =>
                           p <- funApply (f or) args;
                           n <- { n : newRep | AbsR (fst p) n };
                           ret (n, snd p))
                        (fun or =>
                           n <- { n : newRep | AbsR or n };
                           funApply (f' n) args))
    -> refineFun (cod_old_to_new AbsR f)
                 (dom_new_to_old AbsR f').
Proof.
  intros H.
  under_fDom.
    exact (H hnil).
  apply IHfDom; intros.
  exact (H (hcons (B:=id) _ args t0)).
Defined.

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Lemma refineFunMethod :
  forall oldRep newRep (AbsR : oldRep -> newRep -> Prop) fDom fCod
         (f : methodType oldRep fDom (Some fCod))
         (f' : methodType newRep fDom (Some fCod)),
    refineFun (cod_old_to_new AbsR (methodType_to_funType f))
              (dom_new_to_old AbsR (methodType_to_funType f'))
      -> refineMethod AbsR f f'.
Proof.
  unfold dom_new_to_old, refineMethod,
         methodType, methodType_to_funType; simpl in *; intros.
  specialize (H r_o).
  under_fDom.
    rewrite H.
    refine pick val r_n.
      simplify with monad laws; simpl.
      reflexivity.
    exact H0.
  apply IHfDom.
  rewrite H.
  f_equiv.
Defined.

Fixpoint refineFun_AbsR'
         {oldRep newRep}
         (fDom : list Type)
         (fCod : Type)
         (AbsR : oldRep -> newRep -> Prop)
         (fDef : funType fDom (oldRep * fCod))
         (fDef' : funType fDom (newRep * fCod))
         {struct fDom} : Prop :=
  match fDom as fDom'
  return funType fDom' (oldRep * fCod)
           -> funType fDom' (newRep * fCod) -> Prop
  with
  | List.nil =>
    fun fDef fDef' => refine (cod_old_to_new AbsR fDef) fDef'
  | List.cons T fDom' =>
    fun fDef fDef' =>
      forall (t : T), refineFun_AbsR' fDom' fCod AbsR (fDef t) (fDef' t)
  end fDef fDef'.

Definition refineFun_AbsR
           {oldRep newRep}
           (AbsR : oldRep -> newRep -> Prop)
           {fDom : list Type}
           {fCod : Type}
           (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)) : Prop :=
  forall r_o r_n, AbsR r_o r_n
    -> refineFun_AbsR' fDom fCod AbsR (fDef r_o) (fDef' r_n).

Lemma refineFun_AbsR_trans
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef fDef'' : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun fDef fDef''
    -> refineFun_AbsR AbsR fDef'' fDef'
    -> refineFun_AbsR AbsR fDef fDef'.
Proof.
  intros.
  unfold refineFun_AbsR in *.
  induction fDom; simpl in *; intros.
    rewrite H.
    exact (H0 _ _ H1).
  apply (IHfDom (fun r => fDef r t)
                (fun r => fDef'' r t)
                (fun r => fDef' r t)).
  - intros.
    exact (H _ _).
  - intros.
    exact (H0 _ _ H2 _).
  - exact H1.
Qed.

Lemma refineFun_AbsR_trans'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' fDef'' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun fDef'' fDef'
    -> refineFun_AbsR AbsR fDef fDef''
    -> refineFun_AbsR AbsR fDef fDef'.
Proof.
  intros.
  unfold refineFun_AbsR in *.
  induction fDom; simpl in *; intros.
    rewrite (H0 _ _ H1).
    exact (H _).
  apply (IHfDom (fun r => fDef r t)
                (fun r => fDef' r t)
                (fun r => fDef'' r t)).
  - intros.
    exact (H _ _).
  - intros.
    exact (H0 _ _ H2 _).
  - exact H1.
Qed.

Lemma refineFun_To_refineFunAbsR'
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)),
    forall r_o r_n, AbsR r_o r_n
      -> (forall r_o r_n, refineFun_AbsR' fDom fCod AbsR (fDef r_o) (fDef' r_n))
      -> refineFun (cod_old_to_new AbsR fDef) (dom_new_to_old AbsR fDef').
Proof.
  intros.
  unfold refineFun_AbsR', cod_old_to_new, dom_new_to_old in *.
  under_fDom.
    intros.
    rewrite (H0 t r_n).
    unfold refine; intros.
    apply Bind_inv in H1.
    do 2 destruct H1.
    apply Pick_inv in H1.
    admit.
  Fail apply (IHfDom (fun r => H r t)).
Admitted.

Lemma refineFunAbsR_To_refineFun
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef : funType (oldRep :: fDom) (oldRep * fCod))
           (fDef' : funType (newRep :: fDom) (newRep * fCod)),
    refineFun (cod_old_to_new AbsR fDef) (dom_new_to_old AbsR fDef')
    -> refineFun_AbsR AbsR fDef fDef'.
Proof.
  intros.
  unfold refineFun_AbsR, cod_old_to_new, dom_new_to_old.
  under_fDom.
    intros.
    setoid_rewrite H.
    refine pick val r_n.
      simplify with monad laws.
      reflexivity.
    exact H0.
  exact (IHfDom (fun r => H r t) _ _ H0).
Qed.

(*
Lemma refineFun_To_AbsR_refl
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
  : forall (fDef' : funType (newRep :: fDom) (newRep * fCod)),
      refineFun_AbsR AbsR fDef' fDef'.
Proof.
  intros.
  unfold refineFun_AbsR, domcod_new_to_old, cod_new_to_old, dom_new_to_old.
  induction fDom; simpl in *; intros.
    simplify with monad laws.
    refine pick val r_n.
      simplify with monad laws.
      etransitivity.
        apply refine_bind.
          reflexivity.
        intro p; destruct p; simpl.
        refine pick val r_o.
          simplify with monad laws.
          refine pick val n.
            simplify with monad laws.
            reflexivity.
          admit.
        admit.
      simplify with monad laws.
      reflexivity.
    exact H.
  apply (IHfDom (fun r => fDef' r t) r_o r_n H).
Admitted.
*)

Lemma refine_LeastFixedPoint_AbsR
      {oldRep newRep}
      (AbsR : oldRep -> newRep -> Prop)
      {fDom : list Type}
      {fCod : Type}
      (fDef : funType (oldRep :: fDom) (oldRep * fCod)
              -> funType (oldRep :: fDom) (oldRep * fCod))
      (fDef' : funType (newRep :: fDom) (newRep * fCod)
               -> funType (newRep :: fDom) (newRep * fCod))
  : respectful_hetero
      (funType (oldRep :: fDom) (oldRep * fCod))
      (funType (newRep :: fDom) (newRep * fCod))
      (fun _ => funType (oldRep :: fDom) (oldRep * fCod))
      (fun _ => funType (newRep :: fDom) (newRep * fCod))
      (fun f f' => @refineFun_AbsR _ _ AbsR fDom fCod f f')
      (fun rec rec' f f' =>
         @refineFun_AbsR _ _ AbsR fDom fCod f f')
      fDef fDef'
    -> forall (fDef_monotone : forall rec rec',
                  refineFun rec rec'
                  -> refineFun (fDef rec) (fDef rec'))
              (fDef'_monotone : forall rec rec',
                  refineFun rec rec'
                  -> refineFun (fDef' rec) (fDef' rec')),
      refineFun_AbsR AbsR (LeastFixedPoint fDef)
                          (LeastFixedPoint fDef').
Proof.
  unfold LeastFixedPoint, respectful_hetero; intros.
Abort.
(*   destruct (sup_glb (prefixed_point fDef)) as [? ?]; *)
(*   destruct (sup_glb (prefixed_point fDef')) as [? ?]. *)
(*   eapply refineFun_AbsR_trans. *)
(*     Fail eapply (H0 (fDef (refineFun_sup (prefixed_point fDef')))). *)
(*     Fail eapply fDef_monotone. *)
(*     pose proof (proj1 (Is_LeastFixedPoint *)
(*                          (O := @funDefOps (newRep :: fDom) (newRep * fCod)) *)
(*                          _ (fDef'_monotone))). *)
(*     etransitivity. *)
(*       Fail eapply refineFun_To_refineFunAbsR. *)
(*       Fail eapply H. *)
(*       Fail eapply refineFun_To_AbsR_refl. *)
(*     Fail eapply refineFun_To_refineFunAbsR. *)
(*     Fail eapply refineFunAbsR_To_refineFun. *)
(*     reflexivity. *)
(*   Fail eapply refineFun_AbsR_trans'. *)
(*   pose proof (proj2 (Is_LeastFixedPoint *)
(*                        (O := @funDefOps (newRep :: fDom) (newRep * fCod)) *)
(*                        _ (fDef'_monotone))). *)
(*   Fail eapply H5. *)
(*   Fail eapply H. *)
(*   Fail eapply refineFun_To_AbsR_refl. *)
(* Admitted. *)
