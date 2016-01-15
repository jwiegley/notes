Definition search_P_int
        (li: list E | Q li) : {e | P e} :=
  let fix go l x :=
    match l with
      | [l] =>
        exist P l (last_remaining_fulfills l x)
      | cons l (cons lh lt) =>
        let ll := (cons lh lt) in
        match P_dec l with
          | left z => exist P l z
          | right z => go ll (rule_out l ll x z)
        end
      | [] =>
        False_rect {e | P e} (ftf x)
    end in
  go (proj1_sig li) (proj2_sig li).
