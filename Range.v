Definition makeDividedRange `(r : Range rd) `(Hodd : odd before)
  (l1 l2 : NonEmpty UsePos)
  (Heqe : ups rd = NE_append l1 l2)
  (Hu : NE_last l1 < before <= NE_head l2) :
  { p : option RangeSig * option RangeSig | SubRangesOf r Hodd p }.
Proof.
  destruct rd; simpl in *; subst.
  destruct before => //.
  eexists (Some ({| rbeg := rbeg0
                  ; rend := before
                  ; ups  := l1 |}; _),
           Some ({| rbeg := uloc (NE_head l2)
                  ; rend := rend0
                  ; ups  := l2 |}; _)).
  move: (Range_append_spec r).
  move/andP: Hu => [*].
  constructor; auto.
  by apply/andP; split.

  Grab Existential Variables.
  - exact: (Range_append_snd r).
  - exact: (Range_append_fst r).
Defined.
