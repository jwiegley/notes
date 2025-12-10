Generalizable All Variables.

Class Group (G : Set) := {
  e : G;

  inv : G -> G;
  mult : G -> G -> G  where "x * y" := (mult x y);

  left_id : forall x : G, e * x = x;
  left_inv : forall x : G, inv x * x = e;
  assoc : forall x y z : G, x * (y * z) = (x * y) * z
}.

Infix "*" := mult : group_scope.

Open Scope group_scope.

Theorem right_id `{Group G} : forall x : G, x * e = x.
Proof.
  intros x.
  assert (inv x * (x * e) = inv x * x) as H1.
    rewrite assoc.
    rewrite left_inv.
    apply left_id.
  apply left_cancel in H1.
  exact H.
Qed.