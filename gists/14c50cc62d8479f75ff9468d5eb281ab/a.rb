COQC Fiat_matrix/SparseMatrix.v
map = 
fun (A B : Type) (f : A -> B) =>
fix map (l : list A) : list B :=
  match l with
  | nil => nil
  | a :: t => f a :: map t
  end
     : forall A B : Type, (A -> B) -> list A -> list B

Arguments A, B are implicit
Argument scopes are [type_scope type_scope function_scope list_scope]
COQC Fiat_matrix/DenseMatrix.v
Nat.div_unique = 
fun (a b q r : nat) (H : r < b) (H0 : a = b * q + r) =>
Nat.Private_NZDiv.div_unique a b q r (Nat.le_0_l a) 
  (conj (Nat.le_0_l r) H) H0
     : forall a b q r : nat, r < b -> a = b * q + r -> q = a / b

Argument scopes are [nat_scope nat_scope nat_scope nat_scope _ _]
COQC Fiat_matrix/MatrixLemmas.v
COQC Fiat_matrix/optimize_ADT.v
COQC Fiat_matrix/Kalman.v
