session :: SockConfig
        -> ((SockIdentity, SockType, Metadata)
              -> IO (Producer Frame (SafeT IO) (), Consumer Frame (SafeT IO) ()))
        -> IO (Handle, SockAddr)
        -> IO ()
session = undefined
