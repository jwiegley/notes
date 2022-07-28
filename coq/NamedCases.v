(* This was written by Joachim Breitner. See:

   https://www.joachim-breitner.de/blog/777-Named_goals_in_Coq *)

Inductive CaseName := CaseNameI.

Notation "'case' x , t" := (forall {x : CaseName}, t) (at level 200).

Ltac clear_names := try exact CaseNameI.
Ltac named_constructor  := constructor; [ exact CaseNameI | idtac .. ].
Ltac named_econstructor := econstructor; [ exact CaseNameI | idtac .. ].

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.

Set Default Proof Mode "Classic".

Ltac name_cases := ltac2:(
  (* Horribly manual string manipulations. Does this mean I should
     go to the Ocaml level?
  *)
  let strcpy s1 s2 o :=
    let rec go := fun n =>
      match Int.lt n (String.length s2) with
      | true => String.set s1 (Int.add o n) (String.get s2 n); go (Int.add n 1)
      | false => ()
      end
    in go 0
  in
  let concat := fun s1 s2 =>
    let l := Int.add (Int.add (String.length s1) (String.length s2)) 1 in
    let s := String.make l (Char.of_int 95) in
    strcpy s s1 0;
    strcpy s s2 (Int.add (String.length s1) 1);
    s
  in
  Control.enter (let rec go () :=
    lazy_match! goal with
    | [ h1 : CaseName, h2 : CaseName |- _ ] =>
      (* Multiple case names? Combine them (and recurse) *)
      let h := concat (Ident.to_string h1) (Ident.to_string h2) in
      Std.clear [h1; h2];
      let h := Option.get (Ident.of_string h) in
      assert ($h := CaseNameI);
      go ()
    | [ _ : CaseName |- _ ] =>
      (* A single case name? Set current goal name accordingly. *)
      ltac1:(
        (* How to do this in ltac2? *)
        lazymatch goal with
        | [ H : CaseName |- _ ] => refine ?[H]; clear H
        end
      )
    | [ |- _ ] =>
      Control.backtrack_tactic_failure "Did not find any CaseName hypotheses"
    end
  in go)
).
