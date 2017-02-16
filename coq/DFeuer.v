Require Import Hask.Prelude.
Require Import Hask.Data.List.
Require Import Hask.Control.Applicative.

Generalizable All Variables.

Definition star_angle `{Applicative f} {a b} : f a -> f b -> f b :=
  liftA2 (const id).

Infix "*>" := star_angle (at level 42).

Import ApplicativeLaws.

Theorem dfeuer_20160914 (a b c : Type) `{ApplicativeLaws f} :
  forall (k : a -> b) (u : f a) (v : f c),
    fmap k u *> v = u *> v.
Proof.
  unfold star_angle, liftA2; intros.
  rewrite fmap_comp_x; reflexivity.
Qed.

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

Theorem arkeet2 : forall (A : finType) (B : eqType) (f : A -> B),
  inhabited A -> injective f -> exists g, cancel f g.
Proof.
  move=> A B f H1 H2.
  destruct H1.
  exists (fun x : B =>
            match getBy (fun z => let: (p, s) := z in p == x)
                        [seq (f a, a) | a in enum A] with
            | None => X
            | Some y => snd y
            end).
  move=> Y.
  elim: (enum A) => [|z zs IHzs].
    admit.
  rewrite /getBy /= -/getBy.
  rewrite /forFold /= -/forFold.
  Set Printing All.
  rewrite -foldl_cons.
  destruct H1.
  rewrite /cancel.
  move=> x.
  have H0 : injective (fun _ : False => tt).
    by move=> *; contradiction.
  destruct (H False unit (fun (_ : False) => tt) H0).
  exact/x/tt.
Qed.

Definition uncons `(xs : seq a) : option (a * seq a) :=
  match xs with
    | nil => None
    | cons x xs => Some (x, xs)
  end.

Fixpoint dapp {a} (xs ys : seq a) : seq a :=
  match ys with
  | nil => xs
  | y :: ys => dapp (rcons xs y) ys
  end.

Notation "xs <++ ys" := (dapp xs ys) (at level 100).

queueToList (xs <++ ys) = queueToList xs ++ queueToList ys