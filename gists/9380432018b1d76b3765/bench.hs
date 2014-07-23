    vs <- sinkList
        $ (proc x -> do y <- mapC (+1) -< x
                        g <- takeC 1 -< y
                        returnA -< g)
        $ yieldMany ([1..10] :: [Int])
    print (vs :: [Int])
