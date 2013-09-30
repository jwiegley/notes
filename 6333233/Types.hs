mergeSourceUpdateMaps :: Map Prelude.FilePath UpdateSource
                      -> Map Prelude.FilePath UpdateSource
                      -> Map Prelude.FilePath UpdateSource
mergeSourceUpdateMaps = (M.mapMaybe id .) . alignWith f
  where
    f (These (UpdateSource _) DeleteSource) = Nothing
    f (These _ x) = Just x
    f (This x) = Just x
    f (That x) = Just x
