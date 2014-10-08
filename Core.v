Require Import Coq.Unicode.Utf8_core.
Require Import Coq.Program.Tactics.
Require Export Homotopy.Sigma.

Set Automatic Introduction.
Set Implicit Arguments.
Set Shrink Obligations.
Set Universe Polymorphism.

Generalizable Variables A B C D x y.

(* Notation *)

Reserved Notation "x ~> y" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).
Reserved Notation "1".
Reserved Notation "x ~{ C }~> y" (at level 90, right associativity).

Delimit Scope category_scope with category.
Delimit Scope hom_scope with hom.

Open Scope hom_scope.

(* TODO: set up a class for homs, then we can drop all the ob arguments ? *)

(** (based) paths *)

Inductive based_paths {A} (x: A) : A → Type :=
  refl' : based_paths x x.

Inductive paths {A} : A → A → Type :=
  refl : ∀ (x: A), paths x x.

Bind Scope hom_scope with based_paths.
Bind Scope hom_scope with paths.

Arguments paths [A] x y, A x y : rename.
Arguments based_paths [A] x y, A x y : rename.
Arguments refl' [A x], [A] x, A x.
Arguments refl [A x], [A] x, A x.

Hint Resolve refl'.
Hint Resolve refl.

Notation "x ~ y" := (paths x y) (at level 70).

(* an (∞,1)-category / category up to coherent homotopy *)

Record category :=
{ ob               :> Type
; hom              :> ob -> ob -> Type where "x ~> y" := (hom x y)
; id               : ∀ {x}, x ~> x
; compose          : ∀ {x y z}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) ~ (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h ~ f ∘ (g ∘ h)
; right_id         : ∀ {x y} (f : x ~> y), f ∘ @id x ~ f
; left_id          : ∀ {x y} (f : x ~> y), @id y ∘ f ~ f
; id_id            : ∀ {x}, @id x ∘ @id x ~ @id x
}.

Arguments hom C x y : rename.

Infix "~>" := (hom _).
Infix "~{ C }~>" := (hom C) (at level 90, right associativity).

Bind Scope category_scope with category.

Arguments compose [!C x y z] f%hom g%hom : rename.
Arguments compose_assoc [!C w x y z] f%hom g%hom h%hom : rename.
Arguments compose_assoc_op [!C w x y z] f%hom g%hom h%hom : rename.
Arguments id [!C x] : rename.
Arguments right_id [!C x y] f%hom : rename.
Arguments left_id [!C x y] f%hom : rename.
Arguments id_id [!C x] : rename.

Bind Scope hom_scope with hom.

Create HintDb category discriminated.
Create HintDb hom discriminated.

Infix "∘" := (@compose _ _ _ _) : hom_scope.

Hint Resolve compose_assoc compose_assoc_op left_id right_id id_id.
Hint Rewrite left_id right_id @id_id : category.
Hint Rewrite left_id right_id @id_id : hom.

Notation "1" := (id) : hom_scope.

Open Scope hom_scope.
Open Scope category_scope.

Record groupoid  :=
{ groupoid_category :> category
; inverse : ∀ {x y}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y} (f : x ~> y), inverse (inverse f) ~ f
; inverse_left_inverse : ∀ {x y} (f : x ~> y), inverse f ∘ f ~ id
; inverse_right_inverse : ∀ {x y : groupoid_category} (f : x ~> y), f ∘ inverse f ~ id
}.

Notation "p ^" := (@inverse _ _ _ _ _ p) (at level 40) : hom_scope.

Arguments inverse               [!C x y] f%hom : rename, simpl nomatch.
Arguments inverse_inverse       [!C x y] f%hom : rename.
Arguments inverse_left_inverse  [!C x y] f%hom : rename.
Arguments inverse_right_inverse [!C x y] f%hom : rename.

Hint Resolve inverse_inverse inverse_left_inverse inverse_right_inverse.
Hint Rewrite inverse_inverse inverse_left_inverse inverse_right_inverse : category.
Hint Rewrite inverse_inverse inverse_left_inverse inverse_right_inverse : hom.

(** tactics *)

Ltac path_induction :=
  intros; repeat progress (
     match goal with
     | [ p : @paths _ _ _ |- _ ] => destruct p
     | [ p : @based_paths _ _ _ |- _ ] => destruct p
     | _ => idtac
     end
  ).

Obligation Tactic :=
  autounfold; program_simpl; path_induction; auto.

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [eapply inverse; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].

Tactic Notation "by" tactic(tac) := tac; done.

Program Definition ap11 {A B} {f g:A→B} (h:f ~ g) {x y:A} (p:x ~ y) : f x ~ g y := _.
Program Definition ap12 {A B C} {f g:A→B→C} (h:f ~ g) {x y:A} (p:x ~ y) {u v: B} (q : u ~ v) : f x u ~ g y v := _.
Program Definition apD10 {A} {B:A→Type} {f g : ∀ x, B x} (h:f ~ g) : ∀ x, f x ~ g x := _.

Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g); try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.


(** types *)

Program Definition Types : category := {| hom := λ (x y : Type), x -> y |}.
Program Definition Sets : category := {| hom := λ (x y : Set), x -> y |}.

Definition fun_compose := compose (C:=Types).
Infix "∘" := fun_compose : type_scope.

(** Paths *)

Program Definition Paths A : groupoid :=
{| groupoid_category := {| hom := @paths A |} |}.

Definition path_compose {A} := compose (C:=@Paths A).
Definition path_inverse {A} := inverse (C:=@Paths A).

Arguments path_compose [A x y z] f%hom g%hom.
Arguments path_inverse [A x y] f%hom : simpl nomatch.

(* based paths *)

Program Definition BasedPaths A : groupoid :=
{| groupoid_category := {| hom := @based_paths A |} |}.

Definition based_path_compose {A} := compose (C:=@BasedPaths A).
Definition based_path_inverse {A} := inverse (C:=@BasedPaths A).

Arguments based_path_compose [A x y z] f%hom g%hom.
Arguments based_path_inverse [A x y] f%hom.

Program Definition op (C : category) :=
{| hom := λ x y, C y x
 ; id  := @id C
 ; compose := λ _ _ _ f g, compose (C := C) g f
|}.

Program Definition op_groupoid (C : groupoid) : groupoid :=
{| groupoid_category := op C
 ; inverse := λ x y, @inverse C y x
|}.

Record functor (C: category) (D: category) :=
{ map_ob : ob C → ob D
; map : ∀ {x y : ob C}, (x ~> y) → hom D (map_ob x) (map_ob y)
; map_id : ∀ {x : ob C}, map (id (x := x)) ~ id
; map_compose : ∀ {x y z : ob C} (f : y ~> z) (g : x ~> y),
   map f ∘ map g ~ map (f ∘ g)
}.

Hint Rewrite map_id map_compose : category hom.
Hint Resolve map map_id map_compose : category.
Hint Resolve map map_id map_compose : hom.

Arguments map_ob [C%category D%category] F x : rename.
Arguments map [C%category D%category] !F [x y] f%hom : rename.

(* this hack lets us use a functor as its action on morphisms, rather than its action on objects *)
Record > morphism (C: category) :=
{ morphism_x : C
; morphism_y : C
; morphism_f :> morphism_x ~> morphism_y
}.

Hint Unfold morphism_f.

Arguments Build_morphism [C x y] f%hom : rename.

Program Definition path_morphism {A} {a b: A} (p : paths a b) : morphism (Paths A) := Build_morphism p.
Coercion path_morphism : paths >-> morphism.

Program Definition based_path_morphism {A} {a b: A} (p : based_paths a b) : morphism (BasedPaths A) := Build_morphism p.
Coercion based_path_morphism : based_paths >-> morphism.

Program Definition fmap `(f : functor C D) (m : morphism C) : D (map_ob f (morphism_x m)) (map_ob f (morphism_y m)) := map f m.
Coercion fmap : functor >-> Funclass.

Program Definition contramap `(F : functor (op C) D) {x y : C} (f : C x y) := map F f.

(* Probably the first novel development in this file *)

Program Definition ap `(f : A → B) := Build_functor (Paths A) (Paths B) f _ _ _.

Program Definition transport {A : Type} `(P: A → Type) := Build_functor (Paths A) Types P _ _ _.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing).

Program Definition apd {A : Type} {P : A → Type} {x y : A} (f: ∀ (a: A), P a) (p: x ~ y) :
  p # f x ~ f y := _.

Program Definition optransport {A: Type} {P: A → Type} := Build_functor (op (Paths A)) Types P _ _ _.

Program Definition coe := Build_functor (Paths Type) Types _ _ _ _.

Program Definition base {A} {P : A → Type} {u v : sigT P} := Build_functor (Paths A) Types _ _ _ _.

Program Definition based {A} := Build_functor (Paths A) (BasedPaths A) _ _ _ _.

Program Definition debased {A} := Build_functor (BasedPaths A) (Paths A) _ _ _ _.

(* Paulin-Mohring J / based path induction *)
Program Definition J
  {A : Type}  (M : A) (C : ∀ (y : A), (based_paths M y) -> Type)
  (H : C M refl') (N : A) (P : based_paths M N) : C N P := _.

(** Uniqueness of identity *)
Section unique_id.
  Variable C : category.
  Implicit Types x y : C.

  Definition unique_id (id0 id1 : ∀ x, x ~> x)
    (id1_left  : ∀ x y (f : x ~> y), f ~ id1 y ∘ f)
    (id0_right : ∀ x y (f : x ~> y), f ∘ id0 x ~ f)
    (x: C) : id0 x ~ id1 x :=
      id0_right x x (id1 x) ∘ id1_left x x (id0 x).

  Program Definition as_left_id {x y} (f : x ~> y) (i : y ~> y) (H : i ~ id) : i ∘ f ~ f :=
    left_id f ∘ ap (λ i, i ∘ f) H.

  Definition as_right_id {x y} (f : x ~> y) (i : x ~> x) (H: i ~ id) : f ∘ i ~ f :=
    right_id f ∘ ap (compose f) H.
End unique_id.

Arguments unique_id [C] f i H%hom id1_left id0_right : rename.
Arguments as_left_id [C x y] f i H%hom : rename.
Arguments as_right_id [C x y] f i H%hom : rename.

Section inverses.
  Variable C : groupoid.

  Variable x y : C.
  Variable f : C x y.
  Variable g : C y x.

  Program Definition as_left_inverse (H : g ~ inverse f) : g ∘ f ~ id :=
    inverse_left_inverse f ∘ ap (λ g, g ∘ f) H.

  Program Definition as_right_inverse (H : g ~ inverse f) : f ∘ g ~ id :=
    inverse_right_inverse f ∘ ap (compose f) H.

End inverses.

Program Definition id_functor (C : category) := Build_functor C C _ _ _ _.

Program Definition compose_functor {C D E : category}
  (G : functor D E) (F: functor C D) :=
{| map_ob := λ x, map_ob G (map_ob F x)
 ; map := λ x y f, map G (map F f)
 |}.
Obligation 1.
  apply path_compose with (y := map G 1).
  - apply map_id.
  - apply (ap (λ g, map G g) (@map_id C D F x)).
Defined.
Next Obligation.
  apply path_compose with (y := map G (map F f ∘ map F g)).
  - apply (map (ap (λ g, map G g)) (@map_compose C D F x y z f g)).
  - apply map_compose.
Defined.

Program Definition id_id_functor {C}
  : compose_functor (id_functor C) (id_functor C) ~ id_functor C := _.

Program Definition right_id_functor `(f : functor C D)
  : compose_functor f (id_functor C) ~ f := _.
Obligation 1.
  unfold compose_functor, id_functor. simpl.
  unfold id_functor_obligation_1.
  unfold id_functor_obligation_2.
  unfold id_functor_obligation_3.
  unfold id_functor_obligation_4.
  unfold compose_functor_obligation_1.
  unfold compose_functor_obligation_2. simpl.
  destruct f. simpl.
  change map_id0 at 2 with (λ x : C, map_id0 x).
  f_ap.
  - apply @path_compose.
  - admit.
Defined.

Lemma total_paths {A : Type} (P : A → Type) (x y : sigT P)
  (p : x.1 ~ y.1) (q : p # x.2 ~ y.2) : x ~ y.
Proof.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.
  path_induction.
  auto.
Defined.