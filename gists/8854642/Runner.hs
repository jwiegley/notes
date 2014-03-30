instance Hashable UpdateActions where
    hash (UpdateActions upds newt) =
        hash (toList upds) `hashWithSalt` newt
    hashWithSalt x (UpdateActions upds newt) =
        hashWithSalt x (toList upds) `hashWithSalt` newt
