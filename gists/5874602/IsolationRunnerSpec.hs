        it "renames files" $ projTest $ \PTI {..} -> do
            open [("Main.hs", "module Main where\nimport Something")] [] 400

            errs <- errors 400 0
            errs `shouldBe` ProjectResult [(KindError, Just ("Main.hs", 2))]

            ProjectResult gen1 <-
                updateMod 400 "Something.hs" "module Something where"
            errs <- errors 400 gen1
            errs `shouldBe` ProjectResult []

            ProjectResult gen2 <-
                updateMod 400 "Something.hs" "module Something2 where"
            errs <- errors 400 gen2
            errs `shouldBe` ProjectResult
                [(KindError, Just ("Something.hs", 1))]

            void $ deleteMod 400 "Something.hs"
            ProjectResult gen3 <-
                updateMod 400 "Something2.hs" "module Something2 where"
            errs <- errors 400 gen3
            errs `shouldBe` ProjectResult [(KindError, Just ("Main.hs", 2))]
