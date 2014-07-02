{-# LANGUAGE RankNTypes #-}

module Skolem where

data Generator s = Generator
data Generatee s = Generatee

newGenerator :: Generator s
newGenerator = Generator

generate :: Generator s -> (Generator s, Generatee s)
generate = undefined

reduce :: Generatee s -> a
reduce = undefined

runGenerator :: (forall s. ((Generator s -> (Generator s -> a) -> a) -> a)) -> a
runGenerator go = go $ flip ($)

main :: IO ()
main = print $ runGenerator $ \f -> f newGenerator $ \gen ->
    (reduce :: Generatee s -> ()) $ snd $ generate gen
