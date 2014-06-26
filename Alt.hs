{-# LANGUAGE OverloadedStrings #-}

module Alt where

import Control.Applicative
import Control.Monad

main :: IO ()
main =
    let f = (\x -> if x == 1 then Just 4 else Nothing)
        g = (\x -> if x == 3 then Just 7 else Nothing )
    in print $ liftM2 (<|>) f g $ 5
