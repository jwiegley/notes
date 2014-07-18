Class Product `{C : Category objC homC}
  {A B} (P : objC) (p1 : P → A) (p2 : P → B) :=
{ product_ump :
    forall (X : objC) (x1 : X → A) (x2 : X → B),
       exists (u : X → P), x1 ≈ p1 ∘ u /\ x2 ≈ p2 ∘ u
    /\ forall (v : X → P), p1 ∘ v ≈ x1 /\ p2 ∘ v ≈ x2 -> v ≈ u
}.

(* Tuples in the Coq category satisfy the UMP for products. *)
Global Instance Tuple_Product {A B : Type}
  : Product (A * B) (@fst A B) (@snd A B).
Proof.
  intros. constructor. intros.
    apply ex_intro with (x := fun x => (x1 x, x2 x)).
    split.
      reduce. reflexivity.
      split.
        reduce. reflexivity.
        intros. reduce. inv H.
          reduce in H0. specialize (H0 x). rewrite <- H0.
          reduce in H1. specialize (H1 x). rewrite <- H1.
          compute. destruct (v x). reflexivity.
Defined.
