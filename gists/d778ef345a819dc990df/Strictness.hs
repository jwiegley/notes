module Strictness where

(>+-) :: a -> ([a], [b]) -> ([a], [b])
p >+- ~(ps, ts) = (p : ps, ts)

data Command a = Command a deriving Show

parsebs' (Command c : ts) = Command c >+- parsebs' ts

main = do
    parsebs' (Command "blah" : undefined)
