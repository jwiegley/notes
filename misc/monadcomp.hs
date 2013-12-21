{-# LANGUAGE MonadComprehensions #-}

import Control.Monad

g :: IO [Int]
g = return [1, 2, 3]

main :: IO ()
main = do xs <- [ [ x + y | x <- a, y <- b ] | a <- g, b <- g ]
          print xs