data List :: Nat -> [*] -> * where
    Nil  :: List 0 '[]
    Cons :: x -> List n xs -> List (n + 1) (x ': xs)

nth :: Int -> List (n + 1) (x ': xs) -> x
nth 0 (Cons x _)  = x
nth n (Cons _ xs) = nth (pred n) (castWith proof xs)
  where
    proof :: List n xs :~: List (n0 + 1) (x ': xs0)
    proof = undefined
