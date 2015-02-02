toChurch :: Nat -> Church
toChurch Z = \_ -> \y -> y
toChurch (S n) = \x -> \y -> x ((toChurch n) x y)

zero = \x -> \y -> y
one = \x -> \y -> x y
two = \x -> \y -> x (x y)

succ = \x -> \y -> x (x y)

fromChurch :: Church -> Nat
fromChurch f = f S Z
