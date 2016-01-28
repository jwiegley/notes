
Require Import Coq.Lists.List.
Import ListNotations.

Definition find_P {A} (P : A -> Prop) (xs : list A)
  (x : A | List.In x xs /\ P x) : { x : A | P x }.
Proof.
  induction xs; simpl in *.
    destruct x. intuition.
  destruct x.
  destruct a0.
  destruct H.
  let (x0, a) := x in match a with conj _ H0 => exist P x0 H0 end.

(*Section redlizard.

  Variable A : Type.
  Variable P : A -> Prop.
  Hypothesis P_dec : forall x : A, {P x} + {~ P x}.

  Fixpoint getP' (l : list A) : (exists x, In x l /\ P x) -> {x : A | P x}.
    refine match l with
    | [] => fun H => False_rect _ _
    | x :: l' => fun H => if P_dec x then exist _ x _ else getP' l' _
    end.
    - firstorder.
    - auto.
    - simpl in *. firstorder. subst. congruence.
  Defined.

  Print getP'.

  Definition getP : {l : list A | (exists x, In x l /\ P x)} -> {x : A | P x} :=
    fun a => getP' (proj1_sig a) (proj2_sig a).

End redlizard.*)

Variable E : Type.
Variable P : E -> Prop.
Hypothesis P_dec : forall (x : E), {P x} + {~ P x}.

Fixpoint has_one (l: list E) :=
  match l with
    | nil => false
    | cons head tail =>
      match P_dec head with
        | left  _ => true
        | right _ => has_one tail
      end
  end.

Definition Q (l : list E) : Prop := has_one l = true.

Theorem rule_out :
  forall (head:E) (tail:list E),
    Q (head::tail) -> ~ P head -> Q tail.
Proof.
  intros.
  unfold Q in H.
  simpl in *.
  destruct (P_dec head).
  tauto.
  tauto.
Qed.

Theorem last_remaining_fulfills :
  forall (last : E), Q [last] -> P last.
Proof.
  intros.
  unfold Q in H.
  simpl in H.
  destruct (P_dec last); congruence.
Qed.

Definition witlist (l1: list E | Q l1) (l2: list E | Q l2) : Prop :=
  match proj1_sig l1 with
    | h::t => t = (proj1_sig l2)
    | [] => False
  end.

Theorem ftf : (false = true) -> False.
  congruence.
  Show Proof.
Qed.

Require Export Coq.Program.Wf.

Program Fixpoint helper (l : list E) x {measure (length l)} : {e | P e} :=
    match l with
      | [l] =>
        exist P l _
      | cons l (cons lh lt) =>
        let ll := (cons lh lt) in
        match P_dec l with
          | left z => exist P l z
          | right z => helper ll (rule_out l ll x z)
        end
      | [] =>
        False_rect {e | P e} (ftf x)
    end.
Next Obligation.
  apply last_remaining_fulfills.
  apply x.
Defined.
Next Obligation.
  admit.
Defined.
Next Obligation.
  admit.
Defined.

Definition search_P_int
        (li: list E | Q li) : {e | P e} :=
  helper (proj1_sig li) (proj2_sig li).
