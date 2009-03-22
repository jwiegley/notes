splitString :: String -> String -> [String]
splitString = split' []
    where split' acc s str@(x:xs)
              | s `isPrefixOf` str = acc : split' [] s (drop (length s) str)
              | otherwise          = split' (acc ++ [x]) s xs
          split' acc _ [] = [acc]
