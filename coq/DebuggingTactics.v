(* These are from CJ Bell on the Coq Club mailing list. *)

(* Unfolds x everywhere before clearing its body *)
Ltac clearbody' x := cbv delta [x] in *; clearbody x.

(* Test whether an identifier is present in the goal or hyp without
altering it *)
(* if x is present in the goal: idtac, otherwise: fail *)
Ltac test_dep x := ( (cbv delta [x] || fail 1); fail) || idtac.
Ltac test_dep_in x H := ( (cbv delta [x] in H || fail 1); fail) || idtac.

(* Succeeds only if x is 'hidden' in g (i.e. we are unable to match x,
but it is there) *)
Ltac is_hidden_dep_in_constr x g:=
  match g with
  | context[x] => fail 1
  | _ => test_dep x
  end.

(* Lists all 'hidden' identifiers within a goal *)
Ltac show_hidden_deps_in_goal:=
  idtac "Hidden dependencies in goal:";
  try match goal with
  | x: _ |- ?g => is_hidden_dep_in_constr x g; idtac x; fail
  end.

(* Lists all 'hidden' identifiers within a hyp*)
Ltac show_hidden_deps_in_hyp H:=
  idtac "Hidden dependencies in" H ":";
  try match goal with
  | x: _ |- _ => match type of H with
    | context[x] => fail 1
    | _ => test_dep_in x H; idtac x; fail
    end
  end.

(* Lists all 'hidden' identifiers *)
Ltac show_hidden_deps_in_all:=
  try match goal with
  | H: _ |- _ => show_hidden_deps_in_hyp H; fail
  end;
  show_hidden_deps_in_goal.

Tactic Notation "show_hidden_deps" := show_hidden_deps_in_goal.
Tactic Notation "show_hidden_deps" "in" hyp(H) := show_hidden_deps_in_hyp H.
Tactic Notation "show_hidden_deps" "in" "*" := show_hidden_deps_in_all.

Goal let f:=nat in let g:=bool in let m:=true in let n:=0 in True.
 intros f g m n.
 change nat with f in n.
 change bool with g in m.
 Fail test_dep f. (* f is not present *)
 revert m n.
 test_dep f.
 test_dep g.
 show_hidden_deps.
 show_hidden_deps in f.
 show_hidden_deps in *.
 Fail clearbody f.
 clearbody' f.
 clearbody' g.
 exact I.
Qed.
