    letrec {
      go2_a10c [Occ=LoopBreaker] :: [m_p a_q] -> m_p [a_q]

      go2_a10c =
        \ (ds_a10d :: [m_p a_q]) ->
          case ds_a10d of _ {
            [] -> z_a10b;
            : y_a10i ys_a10j ->
              let {
                m'_XTk [Dmd=Just L] :: m_p [a_q]

                m'_XTk = go2_a10c ys_a10j } in
              lvl4_s2zU
                y_a10i
                (\ (x_aSx :: a_q) ->
                   lvl3_s2zV
                     m'_XTk
                     (\ (xs_aSy :: [a_q]) ->
                        lvl2_s2zW (: @ a_q x_aSx xs_aSy)))
          }; } in
    go2_a10c eta_Xq