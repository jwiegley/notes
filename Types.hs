mergeUpdateMaps :: (Maybe a -> Maybe a -> Maybe a)
                -> Map Prelude.FilePath a
                -> Map Prelude.FilePath a
                -> Map Prelude.FilePath a
mergeUpdateMaps f x y =
    M.foldlWithKey'
        (\m k mx -> case mx of
              Nothing -> m
              Just x -> M.insert k x m)
        M.empty
        $ M.unionWith f (M.map Just x) (M.map Just y)

mergeSourceUpdateMaps :: Map Prelude.FilePath UpdateData
                      -> Map Prelude.FilePath UpdateData
                      -> Map Prelude.FilePath UpdateData
mergeSourceUpdateMaps = mergeUpdateMaps f
  where
    f _ x@(Just (UpdateSource _)) = x
    f _ (Just DeleteSource)       = Nothing
    f _ _                         = Nothing
