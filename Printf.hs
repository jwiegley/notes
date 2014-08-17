data List :: Nat -> [*] -> * where
    Nil  :: List 0 '[]
    Cons :: x -> List n xs -> List (n + 1) (x ': xs)

class GetElement a where
    type Result a :: *
    getElement :: Int -> a -> Result a

instance GetElement (List 0 '[]) where
    type Result (List 0 '[]) = Void

instance (GetElement (List n xs)) => GetElement (List (n + 1) (x ': xs)) where
    type Result (List (n + 1) (x ': xs)) = x
    getElement 0 (Cons x _)  = x
    getElement n (Cons _ xs) = getElement(n - 1) xs
