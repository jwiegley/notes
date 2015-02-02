fastNub :: Ord a => [a] -> [a]
fastNub = go Set.empty
  where
    go _ [] = []
    go m (y:ys)
        | shouldDrop = go m ys
        | otherwise  = y : go (Set.insert y m) ys
      where
        shouldDrop :: Bool
        shouldDrop = Set.member y m
