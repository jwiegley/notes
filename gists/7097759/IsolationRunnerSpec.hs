        it "invalid module header" $ harness $ do
            open [ ("Main.hs", [here|
module Main where
import Something
|])
                 , ("Something2.hs", "module Something where")
                 ] [] 401

            errs <- errors 401 0
            errs `shouldBe`
                [ (KindError, Just ("Something2.hs", 1))
                , (KindError, Just ("Main.hs", 2))
                ]
