processHoos :: Int -> [Database] -> Database
processHoos size dbs
  | length dbs > size =
    -- Split the list into 'size' sized chunks and recursively process each
    -- chunk
    let f = processHoos size
    in f $ map f (chunksOf size dbs)

  | otherwise =
    -- Now that we have a list of files < size elements long, we combine the
    -- databases
    concat dbs
