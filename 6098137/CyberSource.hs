    estr2 <- soapRequest
        "TransactionIdentifier"  -- identifies this particular transaction
        "3748807815210178147615" -- the customer's recurring subscription id
        c'submit_authorization_request
        (peekCString . c'ccAuthReply_reasonCode)
    forM_ estr2 $ \str ->
        logDebugN $ "Auth reply reason code: " <> T.pack str
