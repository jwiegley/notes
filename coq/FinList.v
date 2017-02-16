(** This code was written by Daniel Schepler <dschepler@gmail.com>. *)

Require Import List.
Require Import Arith.

Inductive Fin : nat -> Set :=
| FinO : forall {n:nat}, Fin (S n)
| FinS : forall {n:nat}, Fin n -> Fin (S n).

Definition Fin_0_inv (P : Fin 0 -> Type) :
  forall x:Fin 0, P x :=
fun x =>
match x in (Fin z) return
  (match z return (Fin z -> Type) with
   | 0 => P
   | S _ => fun _ => unit
   end x) with
| FinO _ => tt
| FinS _ _ => tt
end.

Definition Fin_Sn_inv {n:nat} (P : Fin (S n) -> Type)
  (PO : P FinO) (PS : forall y:Fin n, P (FinS y)) :
  forall x:Fin (S n), P x :=
fun x =>
match x in (Fin Sn) return
  (match Sn return (Fin Sn -> Type) with
   | 0 => fun _ => unit
   | S n' => fun x => forall (P : Fin (S n') -> Type),
     P FinO -> (forall y:Fin n', P (FinS y)) ->
     P x
   end x) with
| FinO _ => fun P PO PS => PO
| FinS _ y => fun P PO PS => PS y
end P PO PS.

Definition FinS_inv {n:nat} (x:Fin (S n)) :
  option (Fin n) :=
Fin_Sn_inv (fun _ => option (Fin n)) None (@Some _) x.

Fixpoint map_FinS_inv {n:nat} (l : list (Fin (S n))) :
  list (Fin n) :=
match l with
| nil => nil
| cons x l' =>
  let recval := map_FinS_inv l' in
  match FinS_inv x with
  | Some y => cons y recval
  | None => recval
  end
end.

Lemma map_FinS_inv_len_noO :
  forall {n:nat} (l : list (Fin (S n))),
  ~ In FinO l -> length (map_FinS_inv l) = length l.
Proof.
induction l; simpl.
+ reflexivity.
+ destruct a using Fin_Sn_inv; simpl; intuition.
Qed.

Lemma map_FinS_inv_len_NoDup :
  forall {n:nat} (l : list (Fin (S n))),
  NoDup l -> length l <= S (length (map_FinS_inv l)).
Proof.
induction 1; simpl.
+ repeat constructor.
+ destruct x using Fin_Sn_inv; simpl; intros.
  - rewrite map_FinS_inv_len_noO; trivial.
  - auto with arith.
Qed.

Lemma in_map_FinS_inv : forall {n:nat} (l : list (Fin (S n)))
  (y : Fin n), In y (map_FinS_inv l) -> In (FinS y) l.
Proof.
induction l; simpl.
+ trivial.
+ destruct a using Fin_Sn_inv; simpl.
  - auto.
  - destruct 1.
    * left; f_equal; trivial.
    * right; auto.
Qed.

Lemma map_FinS_inv_NoDup : forall {n:nat} (l : list (Fin (S n))),
  NoDup l -> NoDup (map_FinS_inv l).
Proof.
induction 1; simpl.
+ constructor.
+ destruct x using Fin_Sn_inv; simpl.
  - trivial.
  - constructor; trivial. contradict H. apply in_map_FinS_inv; trivial.
Qed.

Theorem fin_list : forall {n:nat} (l : list (Fin n)),
  NoDup l -> length l <= n.
Proof.
induction n.
+ destruct l.
  - trivial.
  - destruct f using Fin_0_inv.
+ intros. apply le_trans with (1 := map_FinS_inv_len_NoDup l H).
  auto using le_n_S, map_FinS_inv_NoDup.
Qed.
