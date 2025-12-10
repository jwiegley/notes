Require Import
  Fiat.ADT
  Fiat.ADTNotation
  ByteString.Lib.Tactics
  ByteString.Lib.Fiat
  ByteString.Lib.FromADT
  Coq.Vectors.Vector.

Ltac inspect :=
  destruct_computations; simpl in *;
  repeat breakdown;
  repeat (destruct_computations; simpl in *;
          repeat breakdown).

Ltac attack_ADT r :=
  pattern r; apply ADT_ind; try eassumption;
  intro midx;
  match goal with
  | [ midx : MethodIndex _ |- _ ] => pattern midx
  end;
  apply IterateBoundedIndex.Iterate_Ensemble_equiv';
  repeat apply IterateBoundedIndex.Build_prim_and;
  try solve [constructor];
  simpl in *; intros;
  simpl in *; destruct_ex; split_and;
  repeat inspect; injections; simpl in *;
  inspect; eauto; intros.

Open Scope string_scope.

Definition emptyS    := "empty".
Definition fromListS := "fromList".
Definition eqbS      := "eqb".
Definition eq_decS   := "eq_dec".

Section Types.

Variable A : Type.

(* The simplest specification of a vector is "a length paired with its
   length". We define what equality means for such vectors, without indicating
   how such equality is to be computed.

   However, even this is too much, because we can derive the length of the
   list from its length! *)
Program Definition VectorSpec := Def ADT {
  rep := list A * nat,

  Def Constructor0 emptyS : rep := ret ([]%list, 0),

  (Build_methDef _
     {| methID    := fromListS
      ; methArity := 0
      ; methDom   := [_]%list
      ; methCod   := None|}
     (fun l => ret (l, length l))),

  Def Binary Method0 eqbS (r1 : rep) (r2 : rep) : rep * bool :=
    b <- { b : bool | decides b (r1 = r2) } ;
    ret (r1, b)

}%ADTParsing.

Theorem proper_length : forall r : Rep VectorSpec, fromADT _ r ->
  length (fst r) = snd r.
Proof. intros; attack_ADT r. Qed.

Theorem to_list_inj : forall (A : Type) (n : nat) (t t0 : Vector.t A n),
  to_list t = to_list t0 -> t = t0.
Proof.
  intros.
Admitted.

(* To actual compute equality, we need to know how to test the elements for
   equality. *)
Variable Aeq_dec : forall x y : A, {x = y} + {x <> y}.

(* Lists with length can be efficiently realized as dependently-typed
   vectors. *)
Theorem DepVector : FullySharpened VectorSpec.
Proof.
  start sharpening ADT.

(* jww (2017-12-21): This code is only needed if we need fromADT witnesses
   to refine methods.

  eapply transitivityT.
  eapply annotate_ADT with
    (methDefs' := icons {|methBody :=  _|}
                 (icons {|methBody :=  _|}
                 (icons {|methBody :=  _|} inil ) ) )
    (AbsR := fun (or : list A * nat) (nr : { n : nat & Vector.t A n }) =>
               fst or = to_list (projT2 nr) /\ snd or = projT1 nr).
  simpl; repeat apply Build_prim_prod; simpl;
  intros; try simplify with monad laws; set_evars.
*)

  hone representation using
    (fun (or : list A * nat) (nr : { n : nat & Vector.t A n }) =>
               fst or = to_list (projT2 nr) /\ snd or = projT1 nr);
  try simplify with monad laws; simpl.

  {
    refine pick val (existT (fun n : nat => t A n) 0 (nil _)).
      finish honing.
    auto.
  }

  {
    refine pick val (existT _ (length d) (of_list d)).
      finish honing.
    simpl.
    rewrite to_list_of_list_opp.
    auto.
  }

  {
    simpl.
    refine pick val
      (VectorEq.eqb _ (fun x y => if Aeq_dec x y then true else false)
                    (projT2 r_n) (projT2 r_n0)).
      simplify with monad laws.
      refine pick val r_n.
        simplify with monad laws.
        finish honing.
      intuition.
    destruct H0, H1.
    destruct r_o, r_o0; simpl in *; subst.
    destruct r_n, r_n0; simpl in *; subst.
    destruct (VectorEq.eqb _ _ _ _) eqn:?; simpl.
      pose proof (eqb_nat_eq _ _ _ _ _ _ Heqb); subst.
      apply VectorEq.eqb_eq in Heqb; subst.
        reflexivity.
      intros.
      destruct (Aeq_dec x y); subst; intuition.
    intro.
    inv H0.
    apply to_list_inj in H2; subst.
    clear -Heqb.
    induction t0; simpl in Heqb.
      discriminate.
    apply IHt0.
    destruct (Aeq_dec h h); subst.
      apply Bool.andb_false_iff in Heqb.
      destruct Heqb.
        discriminate.
      contradiction.
    contradiction.
  }

  finish_SharpeningADT_WithoutDelegation.
Defined.

Definition DepVectorImpl := Eval simpl in projT1 DepVector.

Definition vector_eqb (x y : ComputationalADT.cRep DepVectorImpl) : bool :=
  Eval vm_compute in snd (CallMethod DepVectorImpl eqbS x y).

End Types.

Example vector_equality :
  vector_eqb (Aeq_dec:=PeanoNat.Nat.eq_dec)
             (existT _ 3 [1; 2; 3]%vector)
             (existT _ 3 [1; 2; 3]%vector) = true.
Proof. reflexivity. Qed.
