              | Some (pair bs cs)
                <= equiv_dec bs (rew <- [fun a => tlist B _ a] H2 in tnil) => {
                  | inl _ =>
                    Some (rew [fun a => tlist B a _] H1 in tnil, cs);
                  | _ <= tlist_find_wlist (x ::: xs) ys => {
                    | None => None;
                    | Some (pair ys zs) =>
                      Some (y ::: ys, zs)
                  }
                };
              | None <= tlist_find_wlist (x ::: xs) ys => {
                  | None => None;
                  | Some (pair ys zs) =>
                    Some (y ::: ys, zs)
                }
            };
          | _ <= tlist_find_wlist (x ::: xs) ys => {
              | None => None;
              | Some (pair ys zs) =>
                Some (y ::: ys, zs)
            }
        };
      | _  <= tlist_find_wlist (x ::: xs) ys => {
          | None => None;
          | Some (pair ys zs) =>
            Some (y ::: ys, zs)
        }
      }.

End WList.

Section WListProofsInj.

(* Dependending on the choice of A, this can be either
      Eqdep.EqdepTheory.inj_pair2  (incurs axiom)
   or Eqdep_dec.inj_pair2_eq_dec   (when A is decidable)
*)
Hypothesis inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
    (p; x) = (p; y) -> x = y.

Context {A : Type}.
Context {B : A -> A -> Type}.

Context `{EqDec A}.

Hypothesis B_equiv : forall i j, crelation (B i j).
Hypothesis B_equivalence : forall i j, `{Equivalence (B_equiv i j)}.
Hypothesis B_equiv_dec : forall i j, EquivDec (B_equiv i j).

Import EqNotations.

Open Scope signature_scope.

Definition tequiv {i j : A} := tlist_equiv B_equiv B_equivalence (i:=i) (j:=j).
Arguments tequiv /.

Ltac cleanup H0 H2 H3 IHf Heqo :=
  inversion H0; subst; clear H0;
  specialize (IHf _ _ _ _ _ Heqo);
  rewrite <- !tlist_app_comm_cons;
  try (rewrite <- !tlist_app_comm_cons in IHf);
  simpl in IHf |- *;
  unfold tlist_equiv_obligation_1;
  rewrite eq_dec_refl;
  split; auto;
  try reflexivity.

Lemma tlist_find_wlist_app {i l} (f : tlist B i l)
      {j k} (g : tlist B j k) {pre post} :
  tlist_find_wlist B_equiv B_equivalence B_equiv_dec g f = Some (pre, post)
      -> tequiv f (pre +++ g +++ post).
Proof.
  unfold tequiv; intros.
  generalize dependent k.
  generalize dependent j.
  induction f; intros; simpl in H0.
  - destruct g.
      unfold tlist_find_wlist_obligation_1 in H0.
      destruct (eq_dec i0 i); [|discriminate].
      inversion H0; now subst.
    discriminate.
  - destruct g.
      unfold tlist_find_wlist_obligation_3 in H0.
      destruct (eq_dec i0 i); subst.
        inversion H0; now subst.
      unfold tlist_find_wlist_obligation_2 in H0.
      destruct (tlist_find_wlist _ _ _) eqn:?; [|discriminate].
      destruct p.
      inversion H0; subst.
      now cleanup H0 H2 H3 IHf Heqo.
    destruct (eq_dec i0 i); subst. {
      destruct (eq_dec j0 j); subst. {
        unfold tlist_find_wlist_obligation_7 in H0.
        destruct (equiv_dec _ _). {
          rewrite e.
          unfold tlist_find_wlist_obligation_9 in H0.
          unfold tlist_find_wlist_obligation_7 in H0.
          destruct (tlist_find_wlist _ _ _ g f) eqn:?. {
            destruct p.
            unfold tlist_find_wlist_obligation_5 in H0.
            destruct (equiv_dec _ _). {
              cleanup H0 H2 H3 IHf Heqo.
              rewrite e0 in IHf.
              apply IHf.
            }
            clear Heqo.
            unfold tlist_find_wlist_obligation_4 in H0.
            destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
            destruct p.
            rewrite <- e.
            now cleanup H0 H2 H3 IHf Heqo.
          }
          unfold tlist_find_wlist_obligation_4 in H0.
          destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
          destruct p.
          rewrite <- e.
          now cleanup H0 H2 H3 IHf Heqo0.
        }
        unfold tlist_find_wlist_obligation_9 in H0.
        unfold tlist_find_wlist_obligation_8 in H0.
        destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
        destruct p.
        now cleanup H0 H2 H3 IHf Heqo.
      }
      unfold tlist_find_wlist_obligation_10 in H0.
      destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
      destruct p.
      now cleanup H0 H2 H3 IHf Heqo.
    }
    unfold tlist_find_wlist_obligation_11 in H0.
    destruct (tlist_find_wlist _ _ _ (x0 ::: g) f) eqn:?; [|discriminate].
    destruct p.
    now cleanup H0 H2 H3 IHf Heqo.
Qed.

End WListProofsInj.

Definition nat_triple (i j : nat) : Type := ((nat * nat) * nat)%type.

Definition my_list : tlist nat_triple 0 4 :=
  tcons 1 ((0, 1), 100)
        (tcons 2 ((1, 2), 200)
               (tcons 3 ((2, 3), 300)
                      (tcons 4 ((3, 4), 400)
                             tnil))).

Require Import Coq.Arith.EqNat.

Definition nat_equivb (i j : nat) (x y : nat_triple i j) : Type :=
  match x, y with
    (_, a), (_, b) => a = b
  end.

Program Instance nat_equivalence {i j} : Equivalence (nat_equivb i j).
Next Obligation.
  repeat intro.
  destruct x; simpl; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct x, y; simpl; auto.
Qed.
Next Obligation.
  repeat intro.
  destruct x, y, z; simpl in *; subst; auto.
Qed.

Program Instance nat_equiv_dec {i j : nat} :
  EquivDec (A:=nat) (B:=nat_triple) (i:=i) (j:=j) (nat_equivb i j)
           (H:=@nat_equivalence i j).
Next Obligation.
  destruct x, y.
  destruct (eq_dec n n0).
    subst.
    left; reflexivity.
  right; intro.
  apply n1.
  inversion X.
  reflexivity.
Defined.

Example tlist_find_wlist_nat_ex1 :
  @tlist_find_wlist
    nat nat_triple PeanoNat.Nat.eq_dec nat_equivb
    (fun _ _ => nat_equivalence) (fun _ _ => nat_equiv_dec)
    1 3 (tcons 2 ((1, 2), 200) (tcons 3 ((2, 3), 300) tnil))
    0 4 my_list
    === Some (((0, 1, 100) ::: tnil), ((3, 4, 400) ::: tnil)).
Proof. reflexivity. Qed.

