module ManyOr where

import Text.Parsec.String

manyOr :: Parser a -> Int -> Parser [a]
manyOr p = go
  where
    go 0 = return []
    go n = (:) <$> p <*> go (n-1)

pickFromList :: Parser [a] -> [b] -> Parser b
pickFromList p xs = do
    ys <- p
    let l = length ys
    if l < length xs
        then empty
        else return (xs !! l)