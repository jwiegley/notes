data List :: [*] -> * where
    Nil  :: List '[]
    Cons :: x -> List xs -> List (x ': xs)
