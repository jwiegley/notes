(* Written using The Coq Proof Assistant, version 8.4pl3  *)
Require Import Bool.
Require Import List Wf Program Omega Le Arith.
Require Import Permutation Sorted.

Set Implicit Arguments.

Open Scope list_scope.

Definition gtb (x y: nat) : bool :=
 negb (leb x y).

Lemma partition_length_l {X:Type } : forall f (l:list X),
length (fst (partition f l)) <= length l.
Proof.
  intros f l. induction l.
  simpl. auto. simpl.
  destruct (partition f l) as (g, d).
  destruct (f a). simpl in *. omega.
  simpl in *. omega.
Qed.

Lemma partition_length_r {X:Type } : forall f (l:list X),
length (snd (partition f l)) <= length l.
Proof.
  intros f l. induction l.
  simpl. auto. simpl.
  destruct (partition f l) as (g, d).
  destruct (f a). simpl in *. omega.
  simpl in *. omega.
Qed.

Lemma in_partition_snd {X:Type} : forall f (l:list X) x,
In x (snd (partition f l)) ->
In x l.
Proof.
  intros f l x xIN.
  induction l. inversion xIN.
  simpl in *.
  destruct (partition f l).
  destruct (f a).
  simpl in *. right; auto.
  simpl in *.
  destruct xIN. auto.
  auto.
Qed.


Lemma partition_elements {X:Type} : forall f (l:list X) x,
In x l ->
(In x (fst (partition f l)) \/ In x (snd (partition f l))).
Proof.
  intros f l.
  induction l; intros x Hin.
  simpl in Hin. contradiction.
  simpl. destruct (f a).
  inversion Hin; subst.
  left. destruct (partition f l). 
  simpl. left. reflexivity.
  apply IHl in H. destruct (partition f l).
  inversion H. simpl in *. left. right. assumption.
  simpl in *. right. assumption.
  inversion Hin. destruct (partition f l).
  right. simpl. left. assumption.
  destruct (partition f l). apply IHl in H.
  inversion H. auto. right. simpl in *.
  right. assumption.
Qed.
  
Lemma partition_fst {X:Type} : forall f (l:list X) x,
In x (fst (partition f l)) -> f x = true.
Proof.
  intros f l x.
  induction l; intros Hin.
  inversion Hin. simpl in *.
  destruct (partition f l).
  remember (f a) as fa. destruct fa. simpl in *.
  inversion Hin. congruence. auto.
  simpl in *. auto. 
Qed.


Lemma partition_snd {X:Type} : forall f (l:list X) x,
In x (snd (partition f l)) -> f x = false.
Proof.
  intros f l x.
  induction l; intros Hin.
  inversion Hin. simpl in *.
  destruct (partition f l).
  remember (f a) as fa. destruct fa. auto.
  simpl in *. 
  inversion Hin. congruence. auto. 
Qed.

Lemma partition_permutation {X:Type} : forall f (l:list X),
Permutation l ((fst (partition f l)) ++ (snd (partition f l))).
Proof.
  intros f l.
  induction l.
  simpl. auto.
  simpl. destruct (f a).
  destruct (partition f l).
  simpl in *. auto.
  destruct (partition f l).
  apply Permutation_cons_app.
  assumption.
Qed.

Module qs_experiment.

Program Fixpoint quicksort
        (l:list nat) 
        {measure (length l)} : list nat :=
  match l with
  | nil => nil 
  | x :: xs => 
      match partition (gtb x) xs with
      | (lhs, rhs) => 
        (quicksort lhs) ++ x :: (quicksort rhs)
      end
  end.

Next Obligation of quicksort.
Proof.
  simpl. remember (partition_length_l (gtb x) xs). 
  clear Heql.
  rewrite <- Heq_anonymous in l. 
  simpl in *.
  omega.
Qed.  

Next Obligation of quicksort.
Proof.
  simpl. remember (partition_length_r (gtb x) xs). 
  clear Heql.
  rewrite <- Heq_anonymous in l. 
  simpl in *.
  omega.
Qed.  


Example qs_nil:
  quicksort [] = [].
Proof.
  auto.
Qed.

Example qs_ex1:
  quicksort [3 ; 2 ; 1] = [1 ; 2 ; 3].
Proof.
  compute.
  auto.
Qed.

Example qs_ex2:
  quicksort [5 ; 1 ; 13 ; 1 ; 8 ; 0 ; 3 ; 21 ; 2] 
    = [0 ; 1 ; 1 ; 2 ; 3 ; 5 ; 8 ; 13 ; 21].
Proof.
  compute. reflexivity.
Qed.


End qs_experiment.


Module qs_experiment2.

Program Fixpoint quicksort
        (l:list nat) 
        {measure (length l)} : 
        {sl : list nat | 
          Permutation l sl 
          /\ StronglySorted le sl} :=
  match l with
  | nil => nil 
  | x :: xs => 
      match partition (gtb x) xs with
      | (lhs, rhs) => 
        (quicksort lhs) ++ x :: (quicksort rhs)
      end
  end.

Next Obligation of quicksort.
Proof.
  split; auto. constructor.
Qed.

Next Obligation of quicksort.
Proof.
  simpl. remember (partition_length_l (gtb x) xs). 
  clear Heql.
  rewrite <- Heq_anonymous in l. 
  simpl in *.
  omega.
Qed.  

Next Obligation of quicksort.
Proof.
  simpl. remember (partition_length_r (gtb x) xs). 
  clear Heql.
  rewrite <- Heq_anonymous in l. 
  simpl in *.
  omega.
Qed.  

Lemma SSorted_app : forall l1 l2 p,
StronglySorted le l1 ->
StronglySorted le (p :: l2) ->
Forall (fun x=> le x p) l1 ->
StronglySorted le (l1 ++ (p :: l2)).
Proof.
  intros l1. 
  induction l1.
  intros l2 p SSl1 SSpl2 FAlep.
  simpl. assumption.
  intros l2 p SSl1 SSpl2 FAlep.
  apply SSorted_cons.
  apply IHl1.
  inversion SSl1; auto. auto.
  inversion FAlep; auto.
  apply Forall_forall.
  intros x Hin.
  apply in_app_or in Hin.
  inversion SSpl2; subst.
  inversion SSl1; subst.
  rewrite Forall_forall in *.
  destruct Hin. auto.
  apply (le_trans a p x).
  apply FAlep. left; auto.
  destruct H as [EQ | IN]. omega. 
  eauto.
Qed.


Lemma partition_bool_fst {X:Type} : forall (f : X -> bool) (l : list X) x,
In x (fst (partition f l)) -> f x = true.
Proof.
  intros f l.
  induction l.
  intros x Hin.
  inversion Hin.
  intros x Hin.
  remember (f a).
  simpl in *. 
  rewrite <- Heqb in Hin.
  destruct b.
  destruct (partition f l).
  simpl in Hin.
  destruct Hin. congruence.
  apply IHl. auto.
  destruct (partition f l).
  simpl in Hin.
  apply IHl. auto. 
Qed.


Lemma partition_bool_snd {X:Type} : forall (f : X -> bool) (l : list X) x,
In x (snd (partition f l)) -> f x = false.
Proof.
  intros f l.
  induction l. 
  intros x Hin.
  inversion Hin.
  intros x Hin.
  simpl in *.
  destruct (partition f l).
  remember (f a). destruct b.
  simpl in *. auto.
  simpl in *. inversion Hin.
  congruence. auto.
Qed.

Next Obligation of quicksort.
Proof.
  remember (quicksort_obligation_2 
              quicksort 
              eq_refl 
              Heq_anonymous) as Hrl.
  remember (quicksort_obligation_3 
              quicksort 
              eq_refl 
              Heq_anonymous) as Hrr.
  split.
  (* Proof of Permutation *)
  apply Permutation_cons_app.
  remember (partition_permutation (gtb x) xs) as part_perm.
  clear Heqpart_perm.
  rewrite <- Heq_anonymous in *.
  simpl in part_perm. 
  eapply Permutation_trans. exact part_perm.
  apply Permutation_app.
  compute. destruct (quicksort lhs Hrl) as [qlhs [Hqlp Hqls]].
  auto. 
  compute.
  destruct (quicksort rhs Hrr) as [qrhs [Hqrp Hqrs]].
  auto. 
  (* Proof of StronglySorted *)
  destruct (quicksort lhs Hrl) as [lhs' [Hlperm Hlsort]].
  destruct (quicksort rhs Hrr) as [rhs' [Hrperm Hrsort]].
  simpl.
  apply SSorted_app; auto.
  apply SSorted_cons. auto.
  apply Forall_forall. intros r rIn.
  apply Permutation_sym in Hrperm.  assert (In r rhs). eapply
  Permutation_in. exact Hrperm. auto.
  remember (partition_bool_snd (gtb x) xs r) as pbool. clear Heqpbool.
  rewrite <- Heq_anonymous in pbool. simpl in pbool.
  apply pbool in H.
  unfold gtb in H.
  apply negb_false_iff in H.
  apply leb_complete. auto.
  apply Forall_forall.
  intros xl xlIN.
  apply Permutation_sym in Hlperm. assert (In xl lhs). eapply
  Permutation_in. exact Hlperm. auto.
  remember (partition_bool_fst (gtb x) xs xl) as pbool. clear Heqpbool.
  rewrite <- Heq_anonymous in pbool. simpl in pbool.
  apply pbool in H. unfold gtb in H. 
  apply negb_true_iff in H.
  apply leb_iff_conv in H. omega.
Qed.  

End qs_experiment2.