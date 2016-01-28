Program Fixpoint helper (l : list E) x {measure (length l)} : {e | P e} :=
    match l with
      | [l] =>
        exist P l _
      | cons l (cons lh lt) =>
        let ll := (cons lh lt) in
        match P_dec l with
          | left z => exist P l z
          | right z => helper ll (rule_out l ll x z)
        end
      | [] =>
        False_rect {e | P e} (ftf x)
    end.
Next Obligation.
  apply last_remaining_fulfills.
  apply x.
Defined.
Next Obligation.
  admit.
Defined.
Next Obligation.
  admit.
Defined.

Definition search_P_int
        (li: list E | Q li) : {e | P e} :=
  helper (proj1_sig li) (proj2_sig li).
