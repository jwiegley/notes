primes = reverse . foldl fn []
    where fn acc n
              | n `dividesBy` acc = acc
              | otherwise         = (n:acc)
          dividesBy x (y:ys)
              | y == 1         = False
              | x `mod` y == 0 = True
              | otherwise      = dividesBy x ys
          dividesBy x [] = False
