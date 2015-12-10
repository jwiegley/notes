{-# LANGUAGE DeriveFunctor #-}

module InterpretedFree2 where

import Control.Monad.Free

data ActionF r = Print String r deriving Functor
type Action a  = Free ActionF a

print' :: String -> Action ()
print' str = liftF (Print str ())

main' :: Action ()
main' = print' "Hello"

run :: ActionF (IO a) -> IO a
run (Print str next) = putStrLn str >> next

main :: IO ()
main = iterM run main'
