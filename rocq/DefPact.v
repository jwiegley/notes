Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Lists.List
  Coq.Logic.Classical
  Coq.Logic.ProofIrrelevance
  Coq.Relations.Relation_Definitions
  Coq.Sets.Ensembles
  Coq.Program.Program
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Coq.Sets.Powerset_facts
  Coq.Strings.String
  Coq.Unicode.Utf8.

(* type DefPact i o = i -> o *)
(*   =~ *)
(* type DefPact i o = i -> (forall k. (o -> k) -> k) *)

(* -- Iso: a =~ (forall k. (a -> k) -> k) *)

Definition to {a} : a -> (forall k, (a -> k) -> k) := λ x _ f, f x.

Definition from {a} : (forall k, (a -> k) -> k) -> a := λ k, k _ id.

Lemma to_from_id {a} :
  to (a:=a) ∘ from = @id _.
Proof.
  unfold to, from, compose.
  extensionality g.
  extensionality k.
  extensionality f.
  unfold id.
  enough (∀ a b c (x : a → b) (y : b → c) (z : ∀ r, (a → r) → r),
             y (z b x) = z c (y ∘ x)).
    specialize (H _ _ _ id f g).
    unfold id in H.
    rewrite H.
    rewrite compose_id_right.
    reflexivity.
  intros.
Admitted.

Lemma from_to_id {a} :
  from ∘ to (a:=a) = @id _.
Proof.
  unfold to, from, compose.
  extensionality g.
  reflexivity.
Qed.

Definition DefPact i o := (i -> [PactM o]) → (i -> (forall k, (o -> k) -> k)).

(*
Q: When might the rollback happen?

(defpact payment (payer payer-entity
                  payee payee-entity
                  amount)
  (step-with-rollback payer-entity
      (debit payer amount)
    (credit payer amount))
  (step payee-entity
    (credit payee amount)))

(defpact foo:x
  (step x)
  (step x)
  (step x))
*)
