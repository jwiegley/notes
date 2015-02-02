(** This code modified by John Wiegley <johnw@newartisans.com> from code
    written by Daniel Schepler <dschepler@gmail.com>. *)

Require Import List.
Require Import Arith.
Require Import Coq.Vectors.Fin.

Fixpoint catMaybes {a : Set} (l : list (option a)) : list a :=
  match l with
  | nil => nil
  | cons None xs => catMaybes xs
  | cons (Some x) xs => x :: catMaybes xs
  end.

Definition fin := Coq.Vectors.Fin.t.

Definition fin_Sn_inv {n:nat} (P : fin (S n) -> Type)
  (PO : P F1) (PS : forall y : fin n, P (FS y)) :
  forall x : fin (S n), P x :=
  fun x =>
    match x in (t Sn) return
      (match Sn return (fin Sn -> Type) with
       | 0 => fun _ => unit
       | S n' => fun x => forall (P : fin (S n') -> Type),
         P F1 -> (forall y : fin n', P (FS y)) ->
         P x
       end x) with
    | F1 _ => fun P PO PS => PO
    | FS _ y => fun P PO PS => PS y
    end P PO PS.

Definition FS_inv {n} (x : fin (S n)) : option (fin n) :=
  fin_Sn_inv (fun _ => option (fin n)) None (@Some _) x.

Definition map_FS_inv {n:nat} (l : list (fin (S n))) : list (fin n) :=
  catMaybes (map FS_inv l).

Lemma map_FS_inv_len_noO : forall {n} (l : list (fin (S n))),
  ~ In F1 l -> length (map_FS_inv l) = length l.
Proof.
  induction l; trivial.
  destruct a using fin_Sn_inv; simpl; intuition.
Qed.

Lemma map_FS_inv_len_NoDup : forall {n} (l : list (fin (S n))),
  NoDup l -> length l <= S (length (map_FS_inv l)).
Proof.
  induction 1; simpl.
    apply le_0_n.
  unfold map_FS_inv, catMaybes. simpl.
  destruct x using fin_Sn_inv; simpl; intros.
    fold (@catMaybes).
    pose (map_FS_inv_len_noO l H).
    unfold map_FS_inv in *.
    rewrite e. reflexivity.
  auto with arith.
Qed.

Lemma in_map_FS_inv : forall {n} (l : list (fin (S n))) (y : fin n),
  In y (map_FS_inv l) -> In (FS y) l.
Proof.
  induction l; simpl. trivial.
  destruct a using fin_Sn_inv; simpl. auto.
  destruct 1. left; f_equal; trivial.
  right; auto.
Qed.

Lemma map_FS_inv_NoDup : forall {n:nat} (l : list (fin (S n))),
  NoDup l -> NoDup (map_FS_inv l).
Proof.
  induction 1; simpl. constructor.
  destruct x using fin_Sn_inv; simpl. trivial.
  constructor; trivial.
  contradict H.
  apply in_map_FS_inv; trivial.
Qed.

Theorem fin_list n (l : list (fin n)) : NoDup l -> length l <= n.
Proof.
  induction n as [|n']; intros.
    destruct l as [|hd ?]; trivial; inversion hd.
  apply le_trans with (1 := map_FS_inv_len_NoDup l H).
  auto using le_n_S, map_FS_inv_NoDup.
Qed.
