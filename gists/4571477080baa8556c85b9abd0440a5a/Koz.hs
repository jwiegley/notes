replace :: String -> String -> String -> String
replace _ _ [] = []
replace old new str | old `isPrefixOf` str =
    new ++ replace old new (drop (length old) str)
replace old new (s:str) | otherwise =
    s : replace old new str
