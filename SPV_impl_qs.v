Program Instance Same_set_Equivalence {U} : Equivalence (Same_set U).
Obligation 1.
  constructor; intros x0 H; trivial.
Defined.
Obligation 2.
  constructor; inversion H; trivial.
Defined.
Obligation 3.
  constructor; inversion H; inversion H0; intuition.
Defined.

Add Parametric Relation {U : Type} : (Ensemble U) (Same_set U)
  reflexivity proved by (@Equivalence_Reflexive _ _ Same_set_Equivalence)
  symmetry proved by (@Equivalence_Symmetric _ _ Same_set_Equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ Same_set_Equivalence)
  as Same_set_relation.

Add Parametric Morphism {U} : (Intersection U)
  with signature (Same_set U ==> Same_set U ==> Same_set U)
    as Intersection_iso.
Proof.
  intros.
  inversion H.
  inversion H0.
  split; intros.
    intros x2 ?.
    inversion H5.
    intuition.
  intros x2 ?.
  inversion H5.
  intuition.
Qed.
