Set Implicit Arguments.
Unset Strict Implicit.

Module Axioms.

(************************ PARAMETERS AND AXIOMS ************************)

(*** interpret types as being classical sets ***)

Definition E := Type.

(*** elements of a set are themselves sets ***)

Parameter R : forall x : E, x -> E.  
Axiom R_inj : forall (x : E) (a b : x), R a = R b -> a = b.

(*** a set is determined by its elements ****)

Definition inc (x y : E) := exists a : y, R a = x.
Definition sub (a b : E) := forall x : E, inc x a -> inc x b.

Axiom extensionality : forall a b : E, sub a b -> sub b a -> a = b.

(*** we also need extensionality for general product types ***)

Axiom prod_extensionality :
  forall (x : Type) (y : x -> Type) (u v : forall a : x, y a),
    (forall a : x, u a = v a) -> u = v.

Inductive nonemptyT (t : Type) : Prop := 
  nonemptyT_intro : t -> nonemptyT t.
Inductive nonempty (x : E) : Prop := 
  nonempty_intro : forall y : E, inc y x -> nonempty x.

(*** the axiom of choice on the type level *********************)

Parameter chooseT : forall (t : Type) (p : t -> Prop), nonemptyT t -> t.
Axiom chooseT_pr :
  forall (t : Type) (p : t -> Prop) (ne : nonemptyT t),
    ex p -> p (chooseT p ne).

(*** the replacement axiom: images of a set are again sets *********)

Parameter IM : forall x : E, (x -> E) -> E.

Axiom IM_exists :
  forall (x : E) (f : x -> E) (y : E),
    inc y (IM f) -> exists a : x, f a = y.

Axiom IM_inc :
  forall (x : E) (f : x -> E) (y : E),
    (exists a : x, f a = y) -> inc y (IM f). 

(*** the following actually follow from the above as was shown in the standard
library but we write them as axioms for brevity **************)

Axiom excluded_middle : forall P : Prop, ~ ~ P -> P.
Axiom proof_irrelevance : forall (P : Prop) (q p : P), p = q.

(*** the following axioms can be obtained from the Ensembles library but we
include it here as an axiom; it is used for convenience, allowing us to
replace iff by equality so as to be able to rewrite using equality of
propositions **********************************)

Axiom iff_eq : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.


(*** for convenience we give an axiom fixing the realizations of elements of nat
as being the standard finite ordinals ***)

Axiom nat_realization_O : forall x : E, ~ inc x (R 0). 
Axiom nat_realization_S :
  forall (n : nat) (x : E),
    inc x (R (S n)) = (inc x (R n) \/ x = R n). 

(***** we start to need the following type of thing ***)

Axiom prop_realization : forall x : Prop, R x = x.
Axiom true_proof_realization_empty : forall t : True, R t = R 0.
