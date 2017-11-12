                (label name white
                 <> rect (fromIntegral (nvIntMeta "width" nv))
                         (fromIntegral (nvIntMeta "height" nv))
                           # named node
                           # fc (powerColor (fromIntegral
                                             (nvRealMeta "power" nv) :: Double)))
                        # alignTL
                        # translateX (fromIntegral (nvNum "xpos" nv))
                        # translateY (fromIntegral (h - nvNum "ypos" nv))
