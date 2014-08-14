{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Worker where

data WorkStatus = Employed | Unemployed

data List :: [*] -> * where
    Nil :: List '[]
    Cons :: a -> List as -> List (a ': as)

data Worker :: WorkStatus -> * where
    Employee   :: Worker 'Employed
    FreeSpirit :: Worker 'Unemployed

countEmployees :: List as -> Int
countEmployees Nil = 0
countEmployees (Cons Employee xs) = 1 + countEmployees xs
countEmployees (Cons _ xs) = countEmployees xs

main :: IO ()
main = print $ countEmployees (Cons Employee (Cons FreeSpirit (Cons Employee Nil)))
