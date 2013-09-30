outerJoin :: Ord k => Map k a -> Map k b -> Map k (Maybe a, Maybe b)
outerJoin xs ys = Map.unionWith combine
                  (Map.map (\a -> (Just a, Nothing)) xs)
                  (Map.map (\b -> (Nothing, Just b)) ys)
    where
      combine (Just a, Nothing) (Nothing, Just b) = (Just a, Just b)
      combine _ _ = error "outerJoin: the impossible happened"
