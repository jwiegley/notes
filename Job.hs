data TriSet a b
    = TriSetEmpty
    | TriSetSingleA a
    | TriSetSingleB b
    | TriSetAThenB a b
    | TriSetBThenA b a
    | TriSetABA a b a

injectA :: Monoid a => TriSet a b -> a -> TriSet a b
injectA TriSetEmpty na = TriSetSingleA na
injectA (TriSetSingleA oa) na = TriSetSingleA (oa <> na)
injectA (TriSetSingleB ob) na = TriSetBThenA ob na
injectA (TriSetAThenB oa ob) na = TriSetABA oa ob na
injectA (TriSetBThenA ob oa) na = TriSetBThenA ob (oa <> na)
injectA (TriSetABA oa1 ob oa2) na = TriSetABA oa1 ob (oa2 <> na)
