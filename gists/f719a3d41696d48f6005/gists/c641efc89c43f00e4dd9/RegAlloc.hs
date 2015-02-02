determineLiveIntervals :: Procedure a IRVar -> S.Set LiveInterval
determineLiveIntervals p0
    = S.fromList
    $ Map.elems
    $ foldl' go Map.empty
    $ zip [1..]
    $ map (view nodeMeta)
    $ concatMap blockToList
    $ postorder_dfs (procBody p0)
  where
    go acc (i, v) =
        acc & at v.non (newLiveInterval v) %~ \int ->
            int & intervalStart %~ min i
                & intervalEnd   %~ max i
