mergeUpdateMaps :: (These a a -> Maybe a)
                -> Map Prelude.FilePath a
                -> Map Prelude.FilePath a
                -> Map Prelude.FilePath a
mergeUpdateMaps f = (M.mapMaybe f .) . align

mergeSourceUpdateMaps :: Map Prelude.FilePath UpdateSource
                      -> Map Prelude.FilePath UpdateSource
                      -> Map Prelude.FilePath UpdateSource
mergeSourceUpdateMaps = mergeUpdateMaps f
  where
    f (These _ x@(UpdateSource _)) = Just x
    f _ = Nothing
