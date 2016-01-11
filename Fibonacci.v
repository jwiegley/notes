Require Import Coq.Lists.List.
Import ListNotations.
Goal forall A (l : list A), rev l = [] -> l = [].
Proof.
  intros.
  destruct l.
    reflexivity.
  simpl in H.
  destruct (rev l); simpl; discriminate.
Qed.
