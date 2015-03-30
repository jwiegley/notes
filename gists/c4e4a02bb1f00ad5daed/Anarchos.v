Require Coq.Program.Equality.

Import EqNotations.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Definition ev_sum (n m : nat) (H1 : ev n) (H2 : ev m) : ev (n + m) :=
  let fix proof (n : nat) (H1 : ev n) : ev (n + m) :=
      match H1 with
      | ev_0       => rew <- plus_O_n m in H2
      | ev_SS n' H => ev_SS (n' + m) (proof n' H)
      end in
  proof n H1.

Definition ev_sum' (n m : nat) (H1 : ev n) (H2 : ev m) : ev (n + m) :=
  let fix proof (n : nat) (H1 : ev n) (m : nat) (H2 : ev m) : ev (n + m) :=
      match H1 with
      | ev_0       => rew <- plus_O_n m in H2
      | ev_SS n' H => ev_SS (n' + m) (proof n' H m H2)
      end in
  proof n H1 m H2.
