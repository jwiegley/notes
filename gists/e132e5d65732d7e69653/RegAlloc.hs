determineLiveIntervals :: Procedure a IRVar -> S.Set LiveInterval
determineLiveIntervals p0
    = S.fromList
    $ Map.elems
    $ foldl' go Map.empty
    $ zip [1..]
    $ foldGraphNodes collect (procBody p0) []
  where
    collect node rest =
        execWriter (traverseIRInstr (tell . (:[])) (node^.nodeIRInstr)) ++ rest

    go acc (i, v) =
        acc & at v.non (newLiveInterval v) %~ \int ->
            int & intervalStart %~ min i
                & intervalEnd   %~ max i
