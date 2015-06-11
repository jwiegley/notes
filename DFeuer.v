Require Import Hask.Prelude.
Require Import Hask.Data.List.

Generalizable All Variables.

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
  have H0 : injective (fun _ : False => tt).
    by move=> *; contradiction.
  destruct (H False unit (fun (_ : False) => tt) H0).
  exact/x/tt.
Qed.

(* Every function with a left-sided inverse is injective. *)

Theorem johnw : forall A B (f : A -> B) (g : B -> A), cancel f g -> injective f.
Proof. move=> *; exact: can_inj. Qed.
