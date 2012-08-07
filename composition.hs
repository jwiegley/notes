-- This is what I had before, written the naive way:

search :: FilePath -> FilePath -> Sh [FilePath]
search name dir = findWhen (\path -> return $ (filename path) == name) dir

-- And then this, with just a little more thought:

search :: FilePath -> FilePath -> Sh [FilePath]
search name = findWhen $ return . name (==) . filename
