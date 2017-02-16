{-# LANGUAGE ScopedTypeVariables #-}

import Test.QuickCheck
import Test.Hspec
import Data.Serialize
import Data.Proxy

typeTest :: forall a. (Show a, Eq a, Arbitrary a, Serialize a)
         => String -> Proxy a -> SpecWith ()
typeTest name _ =
  context name $
    it "decode inverses encode" $ property $
      \(x :: a) -> (decode . encode) x == Right x

main :: IO ()
main = hspec $ typeTest "foo" (Proxy :: Proxy Int)
