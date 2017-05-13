                 j <- mkBound 0 (z3Sort intTy)
                 jsym <- mkStringSymbol "j"
                 k <- mkBound 1 intSort
                 ksym <- mkStringSymbol "k"
                 assertShow
                     =<< mkForall [] [jsym] [z3Sort intTy]
                     =<< mkOr =<< sequenceA
                     [ mkLe j _0
                     , mkForall [] [ksym] [intSort]
                       =<< mkOr =<< sequenceA
                       [ mkNot =<< mkSetMember k ints
                       , mkGe j =<< mkApp intEnd [k] ]
                     , mkExists [] [ksym] [intSort]
                       =<< mkAnd =<< sequenceA
                       [ mkSetMember k ints
                       , mkGe j =<< mkApp intBeg [k]
                       , mkLt j =<< mkApp intEnd [k] ]])
