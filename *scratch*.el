        it "issue #1093" $ myTest $ \TI {..} -> do
            replicateM_ 100 $
                start True
                      [("main.hs", "main = putStrLn \"Hi!\" >> getLine")]
                      []
                      Nothing
            pid <- start
                True
                [("main.hs", "main = putStrLn \"Hi!\" >> getLine")]
                []
                Nothing
            expect Nothing pid "Hi!\n"
