Definition plus_comm {n m : nat} : n + m = m + n :=
  match n with
  | O => eq_ind m _ plus_n_O _ eq_refl _
  | S n' => rew (plus_n_Sm _ _) in
            rew (plus_Sn_m _ _) in eq_S _ _ (plus_comm n' m)
  end.
