    hit "issue #1093" $ do
        fuzzCheck $ do
            start $ src "main.hs" "main = putStrLn \"Hi!\" >> getLine"
            "Random delay" ?>
                liftIO . threadDelay <$> gen (choose (50000, 1000000))
        expectSome "Hi!\n"
