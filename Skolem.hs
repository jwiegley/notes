{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Skolem where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

data Generator s = Generator

data Generatee s = Generatee

newGenerator :: Generator s
newGenerator = Generator

generate :: Generator s -> (Generator s, Generatee s)
generate = undefined

runGenerator :: (forall s. ((Generator s
                             -> (Generator s -> (Generator s, Generatee s))
                             -> (Generatee s -> a)
                             -> a)
                            -> a))
             -> a
runGenerator go = go $ \gen generator reduce ->
    let (g1, g2) = generator gen
    in reduce g2

main = runGenerator $ \f -> f newGenerator generate (const ())
