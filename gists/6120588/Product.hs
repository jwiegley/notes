getAccountProducts :: Userid
                   -> SqlPersistR log (Map Text (Entity Product, Int, Cents))
getAccountProducts ownerId = do
    now <- liftIO getCurrentTime
    prods <- select $ from $ \(acct, agr, prod, bundle) -> do
        where_ ( acct^.AccountOwner ==. val ownerId
             &&. agr^.AgreementAccount ==. acct^.AccountId
             &&. ( isNothing (agr^.AgreementExpires)
               ||. agr^.AgreementExpires >. just (val now)
                 )
             &&. bundle^.LicenseBundleAgreement ==. agr^.AgreementId
             &&. bundle^.LicenseBundleProduct ==. prod^.ProductId
               )
        return (prod, 1, licenseBundleCost . entityVal <$> bundle)
    return $ foldl'
        (\m (prod, cnt, Cents cost) ->
          let prodName = productName prod
              details  = M.lookup prodName m
          in case details of
              Nothing -> M.insert prodName (prod, cnt, Cents cost) m
              Just (_, cnt', Cents cost') ->
                  M.insert prodName (prod, cnt + cnt', Cents $ cost + cost') m)
        M.empty prods
