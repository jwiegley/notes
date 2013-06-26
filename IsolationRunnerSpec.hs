        it "renames files" $ projTest $ \PTI {..} -> do
            liftIO $ putStrLn $ "renames 1.."
            open [("Main.hs", "module Main where\nimport Something")] [] 400

            liftIO $ putStrLn $ "renames 2.."
            errs <- errors 400 0
            errs `shouldBe` ProjectResult [(KindError, Just ("Main.hs", 2))]

            liftIO $ putStrLn $ "renames 3.."
            ProjectResult gen1 <-
                updateMod 400 "Something.hs" "module Something where"
            errs <- errors 400 gen1
            errs `shouldBe` ProjectResult []

            liftIO $ putStrLn $ "renames 4.."
            ProjectResult gen2 <-
                updateMod 400 "Something.hs" "module Something2 where"
            errs <- errors 400 gen2
            errs `shouldBe` ProjectResult
                [(KindError, Just ("Something.hs", 1))]

            liftIO $ putStrLn $ "renames 5.."
            ProjectResult gen3 <-
                updateMod 400 "Something2.hs" "module Something2 where"
            errs <- errors 400 gen3
            errs `shouldBe` ProjectResult [(KindError, Just ("Main.hs", 2))]

            liftIO $ putStrLn $ "renames 6.."
