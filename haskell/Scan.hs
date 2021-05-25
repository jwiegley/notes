module Scan where

type Stream a = Int -> a

listToStream :: [a] -> Stream a
listToStream [] = error "Cannot make finite list into stream"
listToStream (x:xs) = \n ->
    if n == 0 then x else listToStream xs (n - 1)

streamToList :: Stream a -> [a]
streamToList f = go 0
  where
    go n = f n : go (n + 1)

-- A casaul stream transform has the restriction that any answer at position N
-- may only consult positions 1-(N-1) from the input.
type StreamTransform a b = Stream a -> Stream b

data Scan a b = Scan {
    step  :: b -> a -> b,
    start :: b
    }

scan :: Scan a b -> StreamTransform a b
scan (Scan f z) = listToStream . scanl f z . streamToList
