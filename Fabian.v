Require Import Setoids.Setoid.
Require Import RelationClasses.
Require Import Classes.Morphisms.
Require Import Program.Basics.

Variable X : Type.
Variable reduce : nat -> X -> X -> Prop.

Notation "s '~>(' i ')' t" :=
  (reduce i s t) (at level 50, format "s  '~>(' i ')'  t").

Axiom reduce_refl :
  forall s i, s ~>(i) s.
Axiom reduce_trans :
  forall s t u i j k, i+j=k -> s ~>(i) t -> t ~>(j) u -> s ~>(k) u.

Lemma Proper_reduce (i j k : nat) :
  i+j = k -> Proper (reduce i --> reduce j ++> impl) (reduce k).
Proof.
Admitted.

Lemma testRewrite s t u i j:
  s ~>(i) t -> t ~>(j) u -> s ~>(i+j) u.
Proof.
  intros R1 R2.
  eapply foo.
    exact R1.
    exact R2.
  apply reduce_refl.
Qed.