mergeVertices :: [Vertex] -> [Vertex] -> ([Vertex], [Vertex])
mergeVertices newVertices oldVertices =
    second reverse $ foldl' step ([], []) (zip newVertices oldVertices)
  where
    step (toScan, bestVertices) (x,y) = (newToScan, bestVertex:bestVertices)
      where
        bestVertex = if getDistance x < getDistance y then x else y
        newToScan
            | getDistance bestVertex /= getDistance y = bestVertex:toScan
            | otherwise = toScan