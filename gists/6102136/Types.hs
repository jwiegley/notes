data ProcessorBackend m
    = (MonadLogger m, MonadError ProcessorError m,
       MonadResource m, MonadIO m)
    => ProcessorBackend
    { authorizationRequest        :: Cents -> m AuthorizationRequestId
    , reverseAuthorizationRequest :: AuthorizationRequestId -> m ()
    , captureAuthorizationRequest :: AuthorizationRequestId
                                  -> m AuthorizationRequestId
    , performSaleRequest          :: Cents -> m CaptureRequestId
    , creditPaymentRequest        :: Cents -> m CreditRequestId
    , voidCaptureRequest          :: CaptureRequestId -> m ()
    , voidCreditRequest           :: CreditRequestId -> m ()
