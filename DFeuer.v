Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrfun.

(* For any injective function f, if there exists a right-sided inverse g,
   g is a two-sided inverse for f. *)

Theorem dfeuer : forall (A B : Type) (g : B -> A) (f : A -> B),
  injective f -> cancel g f -> cancel f g.
Proof. move=> *; exact: inj_can_sym. Qed.

(* Not every injective function has a left-sided inverse. *)

Theorem arkeet :
  ~ (forall A B (f : A -> B), injective f -> exists g, cancel f g).
Proof.
  move=> H.
  have Ha : exists A B (f : A -> B) (Hinj : injective f),
              forall (g : B -> A), ~ cancel f g.
    exists False.
    exists unit.
    exists (fun (_ : False) => tt).
    eexists.
      rewrite /injective.
      move=> x1 x2 Heqe.
      contradiction.
    move=> H0 g.
    apply H0.
    exact tt.
  case: Ha => [? [? [? [Hinj H0]]]].
  move: (H _ _ _ Hinj) => [g ?].
  contradiction (H0 g).
Qed.

(* Every function with a left-sided inverse is injective. *)

Theorem johnw : forall A B (f : A -> B) (g : B -> A), cancel f g -> injective f.
Proof. move=> *; exact: can_inj. Qed.
