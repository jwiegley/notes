Theorem not_not_not : forall P : Prop, not (not (not P)) -> not P.
Proof. intuition. Qed.

Inductive LEM (P : Prop) := P_True : P -> LEM P | P_False : not P -> LEM P.

Theorem not_LEM : forall P : Prop, LEM (not (not P)).
Proof.
  intros.
  right.
  unfold not; intros.
  apply H.
  intros.
Abort.

Section Foo.
Variable X :Type.
Variable Phy: X -> Type.
Definition PhyX := {x:X & Phy x}.

Definition e {x:X} {h:Phy x}: PhyX -> Phy x := fun _ => projT2 (existT _ _ h).