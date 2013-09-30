    go xs ys = Map.unionWith combine
               (Map.map (\a -> (Just a, Nothing)) xs)
               (Map.map (\b -> (Nothing, Just b)) ys)

    combine (Just a, Nothing) (Nothing, Just b) = (Just a, Just b)
    combine _ _ = error "outerJoin: the impossible happened"
