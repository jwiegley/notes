euler015slow :: Int -> Int
euler015slow n = go 0 0
  where go x y
          | x == n && y == n = 1
          | x > n || y > n   = 0
          | otherwise = let l = go x (y + 1)
                            r = go (x + 1) y
                        in seq l $ seq r $ l + r
