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

injectB :: Monoid a => TriSet a b -> b -> TriSet a b
injectB TriSetEmpty nb = TriSetSingleB nb
injectB (TriSetSingleA oa) nb = TriSetAThenB oa nb
injectB (TriSetSingleB _) nb = TriSetSingleB nb
injectB (TriSetAThenB oa _) nb = TriSetAThenB oa nb
injectB (TriSetBThenA _ oa) nb = TriSetAThenB oa nb
injectB (TriSetABA oa1 _ oa2) nb = TriSetAThenB (oa1 <> oa2) nb