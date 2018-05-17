convertEvent :: MHT.Instrument a -> Event
convertEvent (MHT.I_kalmanUpdate x y aRaw bRaw cRaw sRaw) =
    Event { eventName       = pack "kalmanUpdate"
          , eventParams     = [ Number (fromIntegral x)
                              , Number (fromIntegral y)
                              ]
          , eventFmtVersion = pack "1.0"
          , eventProvenance = Nothing
          }
  where
    _a = unsafeCoerce aRaw :: Lin.Matrix Double
    _b = unsafeCoerce bRaw :: Lin.Matrix Double
    _c = unsafeCoerce cRaw :: Lin.Matrix Double
    _s = unsafeCoerce sRaw :: Lin.Matrix Double
