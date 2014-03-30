instance Hashable UpdateActions where
    hash (UpdateActions upds newt) =
        hash (toList upds) `hashWithSalt` newt
