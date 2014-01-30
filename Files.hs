instance MFunctor ResumableSource where
    hoist nat (ResumableSource src m) = ResumableSource (hoist nat src) (nat m)
