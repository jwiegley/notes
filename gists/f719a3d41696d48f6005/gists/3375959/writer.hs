import Data.Monoid              -- imports Control.Monad for us 

-- The Last Monoid is a clever way of accepting new state, while keeping old
-- state if none is supplied by the user's bound function.  How it works:
--
--    Last (Just 10) `mappend` Last (Just 20)       => Last (Just 20)
--    Nothing        `mappend` Last (Just 20)       => Last (Just 20)
--    Last (Just 10) `mappend` Nothing              => Last (Just 10)
--    Nothing        `mappend` Nothing              => Nothing

newtype Writer w a = Writer { runWriter :: (a, w) }

instance (Monoid w) => Monad (Writer w) where
    -- return :: a -> Writer w a
    return x = Writer (x, mempty)

    -- (>>=) :: Writer w a -> (a -> Writer w b) -> Writer w b
    (Writer (a, w)) >>= f = let (a', w') = runWriter $ f a
                            in Writer (a', w `mappend` w')

put :: w -> Writer w ()
put newWriter = Writer ((), newWriter)

------------------------------------------------------------------------

baz :: Int -> Writer (Last Int) Int
baz y = do if y == 0
             then put (Last (Just 10))
             else return ()
           return 5

bar :: Writer (Last Int) Int
bar = do put (Last (Just 20))
         _ <- baz 0
         return 5

foo :: (Int, Last Int)
foo = let (Writer (a, w)) = bar in (a, w)