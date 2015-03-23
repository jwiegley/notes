data Foo a = Foo { getFoo :: [a] }
    deriving Eq

{-@ data Foo a = Foo {
        getFoo :: NonEmpty a
    } @-}

{-@ assume concatMap :: _ -> xs:[a] -> { ys:[b] | size xs == size ys } @-}

instance Monad Foo where
    return x = Foo [x]
    Foo xs >>= f = Foo (concatMap (getFoo . f) xs)

{-@ fooMonadLaw1 :: Eq b => (a -> Foo b) -> a -> True @-}
fooMonadLaw1 :: Eq b => (a -> Foo b) -> a -> Bool
fooMonadLaw1 f x = (return x >>= f) == (f x)
