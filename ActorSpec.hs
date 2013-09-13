        runStdoutLoggingT $ do
            tid <- liftBaseWith $ \runInIO ->
                forkIO $ void $ runInIO $ processJobQueue
                    (helloContext :: ListContext String () () SomeException)
            liftIO $ do
                v <- atomically $ takeTMVar slot
                v `shouldBe` msg
                killThread tid
