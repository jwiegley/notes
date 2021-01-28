        -- Do not store wash losses in the transaction history.
        put $ evs & partsOf (each.filtered (\e -> e^.plKind == WashLoss)).each %~ \e ->
            e & plKind .~ BreakEven
              & plLoss .~ 0