    letrec {
      go2_s12k [Occ=LoopBreaker]
        :: [m_i a_j] -> ([a_j] -> [a_j]) -> m_i [a_j]

      go2_s12k =
        \ (ds_X10D :: [m_i a_j]) (dlist_XTg :: [a_j] -> [a_j]) ->
          case ds_X10D of _ {
            [] -> lvl2_s130 (dlist_XTg ([] @ a_j));
            : m_aSC ms_aSD ->
              lvl3_s2zX
                m_aSC
                (\ (x_aSF :: a_j) ->
                   go2_s12k
                     ms_aSD
                     (\ (x1_a10Y :: [a_j]) ->
                        dlist_XTg (: @ a_j x_aSF x1_a10Y)))
          }; } in
    go2_s12k eta_XB (id @ [a_j])