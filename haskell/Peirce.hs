-- Exercise: prove Pierce’s law <=> law of excluded middle in Haskell

{-# LANGUAGE Rank2Types #-}

module Peirce where

import Data.Void

type Not a  = a -> Void
type Pierce = forall a b. ((a -> b) -> a) -> a
type LEM    = forall a.   Either (Not a) a

callCC_lem :: Pierce -> LEM
callCC_lem callCC = callCC $ \k -> Left (k . Right)

lem_callCC :: LEM -> Pierce
lem_callCC (Left n)  = \k -> k (absurd . n)
lem_callCC (Right p) = \_ -> p
