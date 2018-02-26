Definition optionP {A} (P : relation A) : relation (option A) :=
  fun x y => match x, y with
             | Some x', Some y' => P x' y'
             | None, None => True
             | _, _ => False
             end.

Program Instance optionP_Equivalence {A} (P : relation A) :
  Equivalence P -> Equivalence (optionP P).
Obligation 1.
  intro x.
  destruct x; simpl; trivial.
  reflexivity.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *; trivial.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *; auto;
  firstorder.
Qed.
