{-# LANGUAGE ScopedTypeVariables #-}

module Ishtiaq where

import Data.SBV

main = do
    res <- satWith z3 $
        forSome ["x", "y"] $ \(x :: SWord8) (y :: SWord8) ->
            (x + y .< 15) &&& (x - y .< 7)
    print res
