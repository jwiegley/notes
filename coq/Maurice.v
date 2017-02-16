Require Import Arith.
Require Import Sorting.Sorting.
Require Import List.

Import ListNotations.

Definition insert (x : nat) (l : list nat) :
  forall H : LocallySorted lt l, { l' : list nat | LocallySorted lt l' }.
Proof.
  intros H.
  induction l as [|y ys IHys].
    exists [x].
    apply (LSorted_cons1 lt x).
  destruct (lt_dec x y).
    exists (x :: y :: ys).
    apply (@LSorted_consn nat lt x y ys H).
    assumption.
  apply IHys.
  inversion H. constructor.
  assumption.
Defined.

Definition read_from_file (file_contents : list nat) :
  { l' : list nat | LocallySorted lt l' }.
Proof.
  induction file_contents as [|x xs IHxs].
    exists nil.
    apply LSorted_nil.
  destruct IHxs as [z H].
  apply (insert x z H).
Defined.

(****************************************************************************)

Require Import Sorting.Mergesort.

Module Import NatSort := Sort NatOrder.

Fixpoint leb (x1 y : nat) {struct x1} : bool :=
  match x1 with
  | 0 => true
  | S x' => match y with
            | 0 => false
            | S y' => leb x' y'
            end
  end.

Definition leq x x0 : Prop := is_true (leb x x0).

Definition read_from_file2 (file_contents : list nat) :
  { l' : list nat | LocallySorted leq l' }.
  exists (sort file_contents).
  apply Sorted_LocallySorted_iff.
  apply LocallySorted_sort.
Defined.
