Require Export Coq.Unicode.Utf8.

Inductive Maybe (A : Type) : Type :=
  | Nothing : Maybe A
  | Just : A -> Maybe A.

Arguments Nothing [A].

Fixpoint catMaybes {a} (l : list (Maybe a)) : list a :=
  match l with
    | nil => nil
    | cons Nothing x0 => catMaybes x0
    | cons (Just x) x0 => cons x (catMaybes x0)
  end.

Fixpoint map {a b} (f : a → b) (l : list a) : list b :=
  match l with
    | nil => nil
    | cons x x0 => cons (f x) (map f x0)
  end.

Definition const {a b} (x : a) (_ : b) : a := x.

Lemma zq : ∀ X (l : list X), catMaybes (map (const Nothing) l) = @nil X.
Proof. intros. induction l; auto. Qed.
