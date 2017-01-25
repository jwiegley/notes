module ManyOr where

import Text.Parsec.String

manyOr :: Parser a -> Int -> Parser [a]
manyOr p = go
  where
    go 0 = return []
    go n = (:) <$> p <*> go (n-1)

pickFromList :: Parser [a] -> [b] -> Parser (Maybe b)
pickFromList p xs = do
    ys <- p
    let l = length ys
    return $ if l < length xs
             then Nothing
             else Just (xs !! l)