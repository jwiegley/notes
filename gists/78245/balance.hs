splitAtColons :: String -> [String]
splitAtColons = splitAtColons' []
    where splitAtColons' acc [] = [acc]
          splitAtColons' acc (x:xs)
              | x == ':'  = acc : splitAtColons' [] xs
              | otherwise = splitAtColons' (acc ++ [x]) xs
