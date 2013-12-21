        it "sets setting even with no code" $ projTest $ \PTI {..} -> do
            open [] [] 240
            errs <- errors 240 0
            errs `shouldBe` ProjectResult []

            ProjectResult gen <- settings 240 $ Just ["-XOverloadedStrings"]
            errs <- errors 240 gen
            errs `shouldBe` ProjectResult []
