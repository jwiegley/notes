import Data.Monoid
import Control.Monad

newtype Writer w a = Writer { runWriter :: (a, w) }

instance Monoid Int where
    mappend = (+)
    mempty = 0

instance (Monoid w, Eq w) => Monad (Writer w) where
    -- return :: a -> Writer w a
    return x = Writer (x, mempty)

    -- (>>=) :: Writer w a -> (a -> Writer w b) -> Writer w b
    (Writer (a, w)) >>= f = let (a', w') = runWriter $ f a
                                w''      = if w' == mempty then w else w'
                            in Writer (a', w'')

put :: w -> Writer w ()
put newWriter = Writer ((), newWriter)

------------------------------------------------------------------------

baz :: Int -> Writer Int Int
baz y = do if y == 0
             then put 10
             else return ()
           return 5

bar :: Writer Int Int
bar = do put 20
         _ <- baz 0
         return 5

foo :: (Int, Int)
foo = let (Writer (a, w)) = bar in (a, w)