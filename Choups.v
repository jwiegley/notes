Section test.

(* A sample class *)
Let predicate (n:nat) : Prop := n=1.
Variable a:nat.
Class class  : Prop := {
    condition : predicate a
}.

Section nested_section.

(* The argument on which depend the instance *)
Hypothesis H : (forall (n:nat), n = 1).

Global Instance instance : class.
    split. unfold predicate. apply H.
Defined.

End nested_section.

Axiom H : (forall (n:nat), n = 1).

(* Here, I would like to have an instance of [class], using the previous [instance] *)

(*Context (i : instance H).*)