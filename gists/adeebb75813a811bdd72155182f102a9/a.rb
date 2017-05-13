        Just sol -> mainWith $
            foldr (\(node, NodeVars {..}) ->
                       foldr (\n rest ->
                                  if _nvCore /= sol ^?! ix n.nvCore
                                  then connectOutside n node rest
                                  else rest)
                             ?? nub _nvDeps)
                  (diagram sol) (M.assocs sol)
  where
    diagram sol = hsep 1 $
        let coresUsed =
                getMax (foldMap (Max . (fromIntegral :: Integer -> Int) . _nvCore)
                                (M.elems sol)) in
        flip map [1..coresUsed] $ \core ->
            label ("Core " ++ show core) black # alignB
                <> rect 2 1 # lc white
                <> foldMap (gather core) (M.assocs sol)

    label str color = text str # fontSizeL 0.5 # fc color

    gather :: Int -> (Node, NodeVars Integer ()) -> Diagram B
    gather core (node, NodeVars {..})
        | fromIntegral _nvCore /= core = mempty
        | otherwise =
        let Meta {..} = head _nvMeta in
        (label (show node) white
           <> rect 2.0 (fromIntegral metaLatency) # fc metaColor # named node)
            # alignT
            # translateY (- fromIntegral _nvStartTime)
