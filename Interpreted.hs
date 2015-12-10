module Interpreted where

data Action a = Print String (Action a)
              | Done a

main' :: Action ()
main' = Print "Hello" (Done ())

run :: Action a -> IO a
run (Print str next) = putStrLn str >> run next
run (Done value)     = return value
