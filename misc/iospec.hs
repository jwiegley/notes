module IOSpecTest where

import Test.IOSpec
import Prelude hiding (putStrLn)

foo :: IO ()
foo = putStrLn "Hello"

main = foo