module InterpretedFree where

import Control.Monad.Free

data ActionF r = Print String r
type Action a  = Free ActionF a

main' :: Action ()
main' = Free (Print "Hello" (Pure ()))

run :: Action a -> IO a
run (Free (Print str next)) = do putStrLn str
                                 run next
run (Pure value)            = return value

main :: IO ()
main = run main'
