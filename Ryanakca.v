Definition Injection {U1 U2 : Type} (f : U1 -> U2) : Prop :=
    forall a b : U1, a <> b -> f a <> f b.
  Definition Surjection {U1 U2 : Type} (f : U1 -> U2) : Prop :=
    forall b : U2, exists a : U1, f a = b.
  Definition Bijection {U1 U2 : Type} (f : U1 -> U2) : Prop :=
    Injection f /\ Surjection f.
  Definition Inverse {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
    (forall a, g (f a) = a) /\ (forall b, f (g b) = b).
  Theorem BijectionHasInverse {A B : Prop} :
    forall f : A -> B, Bijection f -> exists g, Inverse f g.
  Proof.
    intros f Bij; destruct Bij as [I S].
    assert (g : B -> A).
    intro b.
    specialize (S b).
    destruct S.
      exact x.
    exists g.
    unfold Injection, Surjection, Inverse in *.
    split; intros.
      
(* Error: Case analysis on sort Type is not allowed for inductive definition ex. *)
