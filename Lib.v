Require Coq.Program.Wf.

Program Fixpoint dep_foldl {A : Type} {B : A -> Type}
  (f : forall b' : A, B b' -> A) (b : A) (v : seq (B b))
  (H : forall b x, seq (B b) -> seq (B (f b x)))
  (Hsize : forall b y ys, size (H b y ys) == size ys)
  {measure (size v)} : A :=
  match v with
  | nil => b
  | y :: ys => @dep_foldl A B f (f b y) (H b y ys) _ _ _
  end.
Obligation 3. by move: Hsize => /(_ b y ys) /eqP ->. Qed.
