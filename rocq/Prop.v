Require Import Unicode.Utf8.
Require Import List EqNat. 

Definition lookup {a} (x:nat) (l:list (nat * a)) : option a := 
  match find (λ p, beq_nat x (fst p)) l with 
    | None => None
    | Some (k,v) => Some v
  end.

Definition domain {a b} (m : list (a* b)) : list a := map (@fst a b) m.

Lemma foo : forall B a0 a m,
  {b : option B | lookup a0 (a :: m) = b}
    = if beq_nat a0 (fst a)
      then {b : option B | Some (snd a) = b }
      else {b : option B | lookup a0 m = b }.
Proof.
  intros.
  unfold lookup.
  destruct a. simpl.
  destruct (beq_nat a0 n); reflexivity.
Qed.

Definition lookup_total {B} : ∀ (m : list (nat * B)) a, In a (domain m) → 
  {b | lookup a m = b}.
Proof.
  induction m; simpl; intros.
    exists None.
    reflexivity.
  unfold lookup.
  destruct a. simpl.
  destruct (beq_nat a0 n) eqn:Heqe.
    eexists.
    reflexivity.
  apply IHm.
  intuition.
  simpl in H0.
  rewrite H0 in Heqe.
  rewrite <- beq_nat_refl in Heqe.
  discriminate.
Defined.