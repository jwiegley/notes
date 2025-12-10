Inductive constructed_list {A : Type} : list A -> Type :=
  | Nil : constructed_list []
  | Cons x xs : constructed_list xs -> constructed_list (x :: xs)
  | App xs ys : constructed_list xs ->
                constructed_list ys -> constructed_list (xs ++ ys).

Arguments Cons {A} x {_} _.
Arguments App {A} {_ _} _ _.

Theorem preorder_direct_constructed (t : tree) :
  constructed_list (preorder_direct t).
Proof.
  induction t; simpl.
    repeat constructor.
  constructor; auto.
Qed.

Fixpoint construct_list `(xs : list A) : constructed_list xs :=
  match xs with
  | nil => Nil
  | cons x xs => Cons x (construct_list xs)
  end.

Definition deconstruct_list `(_ : constructed_list xs) : list A := xs.
Arguments deconstruct_list {_} _ /.

Corollary reconstructed xs : xs = deconstruct_list (construct_list xs).
Proof. auto. Qed.

Corollary construct_app xs ys :
  deconstruct_list (construct_list (xs ++ ys))
    = deconstruct_list (App (construct_list xs) (construct_list ys)).
Proof. reflexivity. Qed.

Fixpoint rebuild (x : A) (xs : list A) : tree :=
  match xs with
  | nil => Leaf x
  | (y :: ys)%list => Branch (Leaf x) (rebuild y ys)
  end.

Lemma rebuild_constructed x xs y ys :
  constructed_list xs ->
  constructed_list ys ->
  preorder_direct (rebuild x (xs ++ y :: ys)%list)
    = (preorder_direct (rebuild x xs) ++ preorder_direct (rebuild y ys))%list.
Proof.
  intros.
  rewrite (reconstructed (xs ++ y :: ys)).
  rewrite construct_app.
  rewrite reconstructed.
  rewrite construct_app.
  induction H; simpl; auto.
    induction H0; simpl; auto.
