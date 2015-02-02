#ifdef DEVELOPMENT
        , spiApproot    = API.Approot $
            fromMaybe "http://localhost" (API.unApproot mapproot)
#else
        , spiApproot    = mapproot
#endif
