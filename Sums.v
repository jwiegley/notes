Definition plusS := "plus".

Section Sums.
  Variable Num : Type.
  Variable zero : Num.
  Variable plus : Num -> Num -> Num.

  Hypothesis zero_plus : forall a, plus zero a = a.
  Hypothesis plus_zero : forall a, plus a zero = a.
  Hypothesis plus_plus : forall a b c, plus a (plus b c) = plus (plus a b) c.

  Definition Summator : ADT _ := ADTRep Num {
    Def Constructor0 newS : rep := ret zero,
    Def Method0 plusS (r : rep) (n : Num) : rep * Num :=
      ret (Let_In (plus r n) (fun n' => (n', n')))
  }%ADTParsing.
End Sums.