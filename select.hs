picks :: [x] -> [(x, [x])]
picks [] = []
picks (x : xs) = (x, xs) : [(y, x : ys) | (y, ys) <- picks xs]

allPairs :: [x] -> [(x, x)]
allPairs xs = [(y, z) | (y, ys) <- picks xs, z <- ys]

prop_picksIdentity xs = map fst (picks xs) == xs
  where types = xs :: [Int]