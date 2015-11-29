escapeGreater10 :: Int -> Cont Int Int
escapeGreater10 num = trace "1..\n" $ do
    x <- trace "2..\n" $ callCC $ \k ->
        if num >= 10
        then do
             trace "3..\n" $ k 0
        else do
             trace "4..\n" $ return (num + 1)
    trace "5..\n" $ return x
