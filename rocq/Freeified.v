Require Import Hask.Control.Monad.Free.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

Inductive Freeified (f : Type -> Type) (a : Type) :
  forall (n : nat), Vector.t Type n -> Type :=
  | Pure' : a -> Freeified f a (nil Type)
  | Join' : forall (t : Type) (n : nat) (ts : Vector.t Type n),
      (t -> Freeified f a ts) -> f t -> Freeified f a (cons Type t _ ts).

Arguments Pure' {f a} _.
Arguments Join' {f a _ n ts} _ _.

Definition example :
  Freeified Comp nat (cons Type Z _ (cons Type Z _ (nil Type))) :=
  Join' (fun x : Z =>
           Join' (fun y : Z =>
                    Pure' (Z.to_nat (x + y)))
                 { z : Z | z = 0%Z })
        { z : Z | z = 0%Z }.

Fixpoint retractified `{Monad f} {n} `(fr : Freeified f a (n:=n) ts) : f a :=
  match fr with
    | Pure' x => pure x
    | Join' _ n ts g h => (h >>= (retractified \o g))%monad
  end.

Eval simpl in retractified example.

Ltac freeify comp :=
  match goal with
    [ |- Freeified Comp ?T ?TS ] =>
    assert { c : Comp T
           & { f : Freeified Comp T TS & refineEquiv (retractified f) c } }
      as freeified
      by (exists comp;
          eexists;
          unfold comp;
          repeat
            match goal with
            | [ |- refineEquiv (retractified _) (Bind ?C _) ] =>
              instantiate (1 := Join' _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retractified (_ ?X)) (Bind ?C _) ] =>
              instantiate (1 := fun X => Join' _ C); unfold id; simpl;
              autorewrite with monad laws;
              apply refineEquiv_bind; [ reflexivity |];
              intros ?; unfold id; simpl
            | [ |- refineEquiv (retractified _) (Return _) ] =>
              instantiate (1 := fun _ => Pure' _); unfold id; simpl;
              autorewrite with monad laws;
              reflexivity
            end);
    exact (projT1 (projT2 freeified))
  end.

(*
Definition foo_Z_free :
  { n : nat & { TS : Vector.t Type n & Freeified Comp Z TS } }.
Proof.
  eexists.
  eexists.
  freeify foo_Z.
Defined.

Definition foo_Z_free' :=
  Eval compute [foo_Z_free projT1 projT2] in projT2 (projT2 foo_Z_free).
Print foo_Z_free'.
*)

Definition natify (f : Z -> nat) {n} {ts : Vector.t Type n}
  (x : Freeified Comp Z (n:=n) ts) :
  {ts' : Vector.t Type n & Freeified Comp nat (n:=n) ts'}.
Proof.
  induction x.
    exists (nil Type).
    apply Pure'.
    exact (f a).
Abort.

(* Eval compute [natify fmap Free_Functor Free_bind foo_Z_free' comp] *)
(*   in natify Z.to_nat foo_Z_free'. *)

Example foo_nat0 : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  set_evars.
  unfold foo_Z in *; simpl.
  unfold refine; intros.
  eapply BindComputes.
    eapply BindComputes.
    evar (c : Comp nat).
    pose proof (transport_nat_Z c {z : Z | (0 <= z < 10)%Z}).
    unfold galois_connection in H1.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
Abort.

Example foo_nat0 : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  unfold foo_Z; simpl.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
  setoid_rewrite (z_to_nat_pick _).
  simplify with monad laws.
  setoid_rewrite <- Nat2Z.inj_add.
Abort.

(* Definition foo_nat0' := *)
(*   Eval compute [foo_nat0 proj1_sig projT1] in foo_nat0. *)
(* Print foo_nat0'. *)

(*
Example foo_nat_bad :
  { c : Comp nat
  | galois_inserted_if (fmap Z.of_nat) (fmap Z.to_nat)
                       (fun z : Z => (0 <= z)%Z) c foo_Z }.
Proof.
  exists (ret 0).
  unfold galois_inserted_if.
  apply transport_nat_Z.
Defined.

Definition foo_nat_bad' :=
  Eval compute [foo_nat_bad proj1_sig projT1] in proj1_sig foo_nat_bad.
Print foo_nat_bad'.
*)

Example foo_nat : Comp nat.
Proof.
  adjust_refine (fmap Z.to_nat foo_Z).
  unfold foo_Z; simpl.
Abort.
(*
  apply transport_nat_Z; simpl.
    intros.
    apply Bind_inv in H.
    do 2 destruct H.
    apply Bind_inv in H0.
    do 2 destruct H0.
    apply Return_inv in H1.
    rewrite <- H1; clear H1.
    apply Pick_inv in H.
    apply Pick_inv in H0.
    abstract omega.
  replace 0%Z with (Z.of_nat 0); trivial.
  replace 10%Z with (Z.of_nat 10); trivial.
  replace 20%Z with (Z.of_nat 20); trivial.
  rewrite z_to_nat_pick; trivial.
  setoid_rewrite (z_to_nat_pick _).
  simplify with monad laws.
  setoid_rewrite <- Nat2Z.inj_add.
  assert (refineEquiv (x0 <- {n : nat | 0 <= n < 10};
                       x1 <- {n : nat | 10 <= n < 20};
                       ret (Z.of_nat (x0 + x1)))
                      (v <- x0 <- {n : nat | 0 <= n < 10};
                            x1 <- {n : nat | 10 <= n < 20};
                            ret (x0 + x1);
                       ret (Z.of_nat v))).
    autorewrite with monad laws.
    reflexivity.
  rewrite H.
  reflexivity.
  Grab Existential Variables.
  abstract omega.
Defined.

Definition foo_nat' := Eval compute [foo_nat proj1_sig projT1] in foo_nat.
Print foo_nat'.
*)
