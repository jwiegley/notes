module Absence where

foo = do
    pure (Note0 length)
    <|> do x <- getOptParam
           Note1 length x
           <|> do y <- getOptParam
                  Note2 length x y
                  <|> do z <- getOptParam
                         Note3 length x y z
