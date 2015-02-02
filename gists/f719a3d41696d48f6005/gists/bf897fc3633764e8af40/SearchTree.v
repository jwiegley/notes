Inductive SearchTree: tree -> Prop :=
(* Getting this right is the most important part of the work,
 *   and it's not completely obvious.
 *)
  | empty : SearchTree E
  | goleft a n b m : SearchTree (T a m b) -> n < m -> SearchTree (T (T a n E) m b).
  | goright a n b m : SearchTree (T a m b) -> n > m -> SearchTree (T (T a m E) n b).

Inductive Contents:  Ensemble Z -> tree -> Prop :=
| Ct_E: Contents Empty_set E
| Ct_S x: Contents (Singleton x) (T E x E)
| Ct_B A B l x r: Contents (Union A B) (T l x r).
