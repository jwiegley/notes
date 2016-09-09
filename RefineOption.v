Require Import Coq.Strings.String PeanoNat Fiat.ADT.

Definition sum (x y : nat) : Comp nat :=
  { z : nat | x < y /\ z = 100 }.

Inductive Tele (A B : Type) :=
  | Error : string -> Tele A B
  | Value : B -> Tele A B
  | Put : A -> Tele A B -> Tele A B
  | Get : (A -> Tele A B) -> Tele A B.

Fixpoint runs_to {A B} (t : Tele A B) (v : B) : Prop :=
  match t with
  | Error _ => False
  | Value x => x = v
  | Put x next => runs_to next v
  | Get f => exists x : A, runs_to (f x) v
  end.

Open Scope string_scope.

Lemma final_refinement :
  { f : nat -> nat -> Tele string nat
  | forall x y z, runs_to (f x y) z -> sum x y ↝ z }.
Proof.
  exists (fun x y =>
            Put "Hello"
                (Get (fun input =>
                        if string_dec input "run"
                        then if x <? y
                             then Value _ 100
                             else Error _ _ "Could not realize specification"
                        else (* If this were [Value _ 200], the refinement
                                would not be possible. *)
                             Error _ _ "Could not realize specification"))).
  intros.
  simpl in H; destruct H.
  destruct (string_dec x0 "run"); subst.
    destruct (x <? y) eqn:Heqe;
    simpl in H; subst.
      apply PickComputes.
      intuition.
      apply Nat.ltb_lt; assumption.
    contradiction H.
  contradiction H.
Qed.
