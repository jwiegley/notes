nth :: [a] -> Int -> Maybe a
nth [] _     = Nothing
nth (x:_) 0  = Just x
nth (_:xs) n = nth xs (pred n)

 -- f-algebra = f a -> a

data ListF a r = Nil | Cons a r deriving Functor

type List a = Fix (ListF a)

nth' :: List a -> Int -> Maybe a
nth' = cata phi
  where
    phi :: ListF a (Int -> Maybe a) -> Int -> Maybe a
    phi Nil        _ = Nothing
    phi (Cons k _) 0 = Just k
    phi (Cons _ k) n = k (pred n)

data ListF a r = Nil | Cons a r deriving Functor

type List a = Fix (ListF a)

nth' :: List a -> Int -> Maybe a
nth' = cata phi
  where
    phi :: ListF a (Int -> Maybe a) -> Int -> Maybe a
    phi Nil        _ = Nothing
    phi (Cons k _) 0 = Just k
    phi (Cons _ k) n = k (pred n)

forall n. (forall x (l : ListF a x), length l < n -> x) -> forall x. VectorF a n x -> x
