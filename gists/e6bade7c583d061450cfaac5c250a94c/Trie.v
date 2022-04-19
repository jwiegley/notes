Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Fun.
Require Export Category.Instance.Coq.
Require Export Category.Instance.Sets.
Require Export Coq.Vectors.Vector.

Import VectorNotations.

Generalizable All Variables.
Set Primitive Projections.
(* Set Universe Polymorphism. *)
(* Unset Transparent Obligations. *)

Fixpoint concat `(xs : t (t a n) m) : t a (m * n) :=
  match xs with
  | nil _ => nil a
  | cons _ hd n tl => append hd (concat tl)
  end.

Program Fixpoint group_dep {a : Type} (m n : nat) (xs : t a (m * n)) :
  ∃ xss : t (t a n) m, xs = concat xss :=
  match m with
  | O => (nil _; _)
  | S m' =>
      match splitat n xs with
      | (ys, zs) => let (zss, H) := group_dep m' n zs
                    in (cons _ ys _ zss; _)
      end
  end.
Next Obligation.
  destruct (mult_n_O n); simpl.
  now destruct xs using case0.
Qed.
Next Obligation.
  destruct (mult_n_Sm n m'); simpl.
  destruct (PeanoNat.Nat.add_comm n (n * m')); simpl.
  symmetry in Heq_anonymous.
  apply append_splitat in Heq_anonymous.
  rewrite Heq_anonymous.
  reflexivity.
Qed.

Definition group {a : Type} (m n : nat) (xs : t a (m * n)) : t (t a n) m :=
  `1 (group_dep m n xs).

Lemma map_append `(f : a -> b) `(xs : t a n) `(ys : t a m) :
  map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  induction xs; simpl.
  - reflexivity.
  - now rewrite IHxs.
Qed.

Lemma map_concat `(f : a -> b) `(xs : t (t a n) m) :
  map f (concat xs) = concat (map (map f) xs).
Proof.
  induction xs; simpl.
  - now destruct (mult_n_O n).
  - destruct (mult_n_Sm n n0); simpl.
    destruct (PeanoNat.Nat.add_comm n (n * n0)); simpl.
    rewrite <- IHxs.
    now apply map_append.
Qed.

(**************************************************************************)

Inductive Shape :=
  | Bottom
  | Top
  | Plus (x y : Shape)
  | Times (x y : Shape).

Fixpoint size (s : Shape) : nat :=
  match s with
  | Bottom => 0
  | Top => 1
  | Plus x y => size x + size y
  | Times x y => size x * size y
  end.

Fixpoint unsize (n : nat) : Shape :=
  match n with
  | O => Bottom
  | S n => Plus Top (unsize n)
  end.

Theorem size_unsize n : size (unsize n) = n.
Proof. now induction n; simpl; auto. Qed.

Theorem unsize_size : (∀ s, unsize (size s) = s) -> False.
Proof.
  intros.
  specialize (H Top).
  simpl in H.
  inversion H.
Qed.

Program Instance Shape_Setoid : Setoid Shape := {|
  equiv := λ x y, size x = size y
|}.

(**************************************************************************)

Inductive Trie (a : Type) : Shape -> Type :=
  | Unit : Trie a Bottom             (* a^0 = 1 *)
  | Id : a -> Trie a Top             (* a^1 = a *)
    (* a^(b+c) = a^b * a^c *)
  | Join {x y} : Trie a x -> Trie a y -> Trie a (Plus x y)
    (* a^(b*c) = (a^b)^c *)
  | Joins {x y} :
    (* This allows us to positively express Trie (Trie a y) x *)
    forall z, (z -> Trie a y) -> Trie z x -> Trie a (Times x y).

Arguments Unit {a}.
Arguments Id {a} _.
Arguments Join {a x y} _ _.
Arguments Joins {a x y} _ _ _.

Fixpoint vec `(x : Trie a s) : Vector.t a (size s) :=
  match x with
  | Unit         => nil a
  | Id x         => cons a x 0 (nil a)
  | Join xs ys   => vec xs ++ vec ys
  | Joins _ k xs => concat (map (vec ∘ k) (vec xs))
  end.

Program Fixpoint trie `(x : Vector.t a (size s)) : Trie a s :=
  match s with
  | Bottom    => Unit
  | Top       => Id (@hd a 0 x)
  | Plus s t  => let (ys, zs) := splitat (size s) x
                 in Join (trie ys) (trie zs)
  | Times s t => Joins (Vector.t a (size t)) trie
                       (trie (group (size s) (size t) x))
  end.

Fixpoint vec_trie `(x : Vector.t a (size s)) : vec (trie x) = x.
Proof.
  induction s; simpl in *.
  - now induction x using case0.
  - induction x using caseS'.
    simpl.
    now induction x using case0.
  - destruct (splitat (size s1) x) eqn:Heqe; simpl in *.
    apply append_splitat in Heqe.
    rewrite Heqe; clear Heqe.
    rewrite IHs1.
    rewrite IHs2.
    reflexivity.
  - unfold group.
    destruct (group_dep _ _ _) eqn:Heqe; simpl in *.
    subst.
    f_equal.
    rewrite vec_trie.
    clear -vec_trie.
    induction x0; simpl; auto.
    rewrite IHx0.
    now rewrite vec_trie.
Qed.

Definition Trie_equiv {s : Shape} {a : Type} (x y : Trie a s) : Type :=
  vec x = vec y.

Arguments Trie_equiv {s a} x y /.

Program Instance Trie_Setoid {s : Shape} {a : Type} : Setoid (Trie a s) := {|
  equiv := Trie_equiv
|}.
Next Obligation.
  unfold Trie_equiv.
  constructor; repeat intro; intuition.
  now rewrite H, H0.
Qed.

Program Instance vec_Proper {a : Type} {s : Shape} :
  Proper (equiv ==> eq) (@vec a s).

Theorem trie_vec `(x : Trie a s) : trie (vec x) ≈ x.
Proof. now simpl; rewrite vec_trie. Qed.

Fixpoint Trie_map {s : Shape} `(f : a -> b) (x : Trie a s) : Trie b s :=
  match x with
  | Unit => Unit
  | Id x => Id (f x)
  | Join xs ys => Join (Trie_map f xs) (Trie_map f ys)
  | Joins z k xs => Joins z (Trie_map f ∘ k) xs
  end.

Fixpoint Trie_map_flatten `(f : a -> b) `(t : Trie a s) :
  vec (Trie_map f t) = map f (vec t).
Proof.
  induction t; try (simpl; reflexivity).
  - simpl.
    rewrite map_append.
    now rewrite IHt1, IHt2.
  - simpl in *.
    rewrite map_concat.
    rewrite map_map.
    f_equal.
    clear -Trie_map_flatten.
    induction (vec t0); simpl; auto.
    rewrite IHt1.
    now rewrite Trie_map_flatten.
Qed.

Program Instance Trie_map_Proper {s : Shape} `{f : a -> b} :
  Proper (equiv ==> equiv) (@Trie_map s a b f).
Next Obligation.
  proper.
  rewrite !Trie_map_flatten.
  now rewrite X.
Qed.

(**************************************************************************)

Program Instance Trie_Functor (s : Shape) : Coq ⟶ Sets := {|
  fobj := λ a,     {| carrier   := Trie a s
                    ; is_setoid := Trie_Setoid |};
  fmap := λ _ _ f, {| morphism := Trie_map f
                    ; proper_morphism := Trie_map_Proper |}
|}.
Next Obligation.
  proper.
  rewrite !Trie_map_flatten.
  induction (vec x1); simpl; auto.
  now rewrite H, IHt.
Qed.
Next Obligation.
  rewrite Trie_map_flatten.
  now rewrite map_id.
Qed.
Next Obligation.
  rewrite !Trie_map_flatten.
  now rewrite map_map.
Qed.

Program Definition Tries (a : Type) : Category := {|
  obj     := Shape;
  hom     := λ x y,
    (* This is a setoid morphism within a smaller category than Coq. *)
    ∃ f : Trie a x -> Trie a y, Proper (equiv ==> equiv) f;
  homset  := λ _ _, {| equiv := fun f g => ∀ x, `1 f x ≈ `1 g x |};
  id      := _;
  compose := _
|}.
Next Obligation.
  equivalence.
  simpl in *.
  now rewrite H1, H2.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H.
  now apply e1, H0.
Qed.

Program Definition Vectors (a : Type) : Category := {|
  obj     := nat;
  hom     := λ x y, Vector.t a x -> Vector.t a y;
  homset  := λ _ _, {| equiv := fun f g => ∀ x, f x = g x |};
  id      := λ _, id
  (* jww (2021-12-29): Uncommenting this line results in
     Error: <in exception printer>:<original exception:Anomaly "Uncaught exception Not_found."
     on the next Qed.
   *)
  (* ; compose := λ x y z f g, λ w, f (g w) *)
|}.
Next Obligation.
  equivalence.
  now rewrite H1, H2.
Qed.
Next Obligation.
  proper.
  unfold Vectors_obligation_2.
  now rewrite H0, H.
Qed.

Program Definition Cardinality (a : Type) : Tries a ⟶ Vectors a := {|
  fobj := size;
  fmap := λ _ _ f, vec ∘ `1 f ∘ trie
|}.
Next Obligation.
  now rewrite vec_trie.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  apply X0; simpl.
  now rewrite trie_vec.
Qed.

Definition sized `(x : t a (size (unsize n))) : t a n.
Proof. now rewrite size_unsize in x. Defined.

Definition resized `(x : t a n) : t a (size (unsize n)).
Proof. now rewrite <- size_unsize in x. Defined.

Lemma resized_sized `(x : t a (size (unsize n))) : resized (sized x) = x.
Proof.
  unfold sized, resized.
  now destruct (size_unsize n); simpl.
Qed.

Lemma sized_resized `(x : t a n) : sized (resized x) = x.
Proof.
  unfold sized, resized.
  Import EqNotations.
  assert (∀ x, rew [t a] size_unsize n in
               rew <- [t a] size_unsize n in x = x).
    now destruct (size_unsize n); simpl.
  now rewrite H.
Qed.

Program Definition Canonicity (a : Type) : Vectors a ⟶ Tries a := {|
  fobj := unsize;
  fmap := λ _ _ f, (trie ∘ resized ∘ f ∘ sized ∘ vec; _)
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  now rewrite H.
Qed.
Next Obligation.
  rewrite resized_sized.
  now apply trie_vec.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.

Program Definition Card_Canon_Adjunction a :
  Cardinality a ⊣ Canonicity a := {|
  adj := λ x y,
    {| to   := {| morphism := λ f, (trie ∘ resized ∘ f ∘ vec; _) |}
     ; from := {| morphism := λ f, sized ∘ vec ∘ _ ∘ trie |} |}
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  proper.
  now rewrite H.
Qed.
Next Obligation.
  proper.
  unfold Card_Canon_Adjunction_obligation_3.
  now rewrite H.
Qed.
Next Obligation.
  rewrite !vec_trie.
  rewrite resized_sized.
  apply X.
  now apply trie_vec.
Qed.
Next Obligation.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  rewrite !vec_trie.
  do 2 f_equal.
  apply X.
  now apply trie_vec.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  f_equal.
  apply X0.
  simpl.
  now rewrite trie_vec.
Qed.
Next Obligation.
  unfold Vectors_obligation_2.
  rewrite !vec_trie.
  now rewrite sized_resized.
Qed.

Print Assumptions Card_Canon_Adjunction.