{-# LANGUAGE RankNTypes #-}

module Skolem where

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
    let (_, g) = generator gen
    in reduce g

main :: IO ()
main = runGenerator $ \f -> f newGenerator generate (const ())
