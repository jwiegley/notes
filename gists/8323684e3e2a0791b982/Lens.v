Inductive pnat : Prop := pz : pnat | ps : pnat -> pnat.

Inductive plt : pnat -> pnat -> Prop :=
  | LtZ x   : plt pz (ps x)
  | LtS x y : plt x y -> plt (ps x) (ps y).

Lemma pnat_wf_ind :
  forall (P : pnat -> Type),
         (forall m : pnat, (forall n : pnat, plt n m -> P n) -> P m) ->
    forall n, P n.
Proof.
  move=> P Pwf n.
Abort.
