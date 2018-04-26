        capKindDef <- do
            xs <- forM (zip [0 ..] metaCaps) $ \(c, cp) ->
                mkImplies
                    <$> (mkEq cidx =<< mkIntNum c)
                    <@> (mkEq <$> mkApp capKind [cidx]
                              <@> mkIntNum (cp^.capabilityKind.symIndex))
            mkAnd xs
