Require Import Coq.Classes.RelationClasses.

Class rect_name_for (T : Type) : Type := rect_dummy : T -> Type.
Hint Extern 0 (rect_name_for ?T) => (let x := fresh in intro x; induction x; exact Set) : typeclass_instances.
Ltac head_under_binders term :=
  match eval cbv beta in term with
  | ?f _ => head_under_binders f
  | (fun x => ?f _) => head_under_binders f
  | (fun x => ?f) => head_under_binders f
  | (fun x : ?T => ?f _) => head_under_binders (fun x : T => f)
  | ?term' => term'
  end.
Ltac get_rect ty :=
  let x := constr:(_ : rect_name_for ty) in
  head_under_binders x.
Ltac fill_with_type_vars rect ty :=
  match ty with
  | ?f ?x => let rect' := fill_with_type_vars rect f in
             constr:(rect' x)
  | _ => rect
  end.
Ltac fill_with_type_vars_of rect term :=
  let T := type of term in
  fill_with_type_vars rect T.
Ltac fill_with_evars_then rect x cont :=
  idtac;
  let T := type of rect in
  lazymatch (eval cbv beta in T) with
| forall (a : ?A) (b : @?B a), _
  => let v := fresh in
     first [ revert x; evar (v : A); intro x
           | evar (v : A) ];
       let v' := (eval unfold v in v) in
       fill_with_evars_then
         (rect v')
         x
         cont;
         subst v
| _ => cont (rect x)
end.

Ltac rel_aware_destruct_helper x do_destruct :=
  idtac;
  let T := type of x in
  let rect0 := get_rect T in
  let rect := fill_with_type_vars_of rect0 x in
  let R := match goal with |- ?R ?LHS ?RHS => R end in
  let LHS := match goal with |- ?R ?LHS ?RHS => LHS end in
  let Px := type of LHS in
  let P := match (eval pattern x in Px) with ?P _ => P end in
  let rect := constr:(rect P) in
  fill_with_evars_then
    rect x
    ltac:(fun rect
          => refine (transitivity (y := rect) _ _));
    [ do_destruct x rect0
    | ].

Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?e] ]
           => is_evar e;
             let e' := fresh "e" in
             set (e' := e)
         end.

Ltac subst_evars :=
  repeat match goal with
         | [ H := ?e |- _ ] => is_evar e; subst H
         end.
Ltac destruct_for_refine x :=
  rel_aware_destruct_helper
    x
    ltac:(fun k rect =>
            destruct k;
          set_evars; simpl rect);
  [ ..
  | try (subst_evars; reflexivity) ].

Goal forall n, exists x, match n with 0 => 0 | S _ => 1 end = x.
Proof.
  intro n.
  eexists.
  destruct n.
    reflexivity.
Abort.

Goal forall n, exists x, match n with 0 => 0 | S _ => 1 end = x.
Proof.
  intro n.
  eexists.
  destruct_for_refine n; subst_evars.
    reflexivity.
  instantiate (1 := fun _ _ => 1).
  reflexivity.
Qed.