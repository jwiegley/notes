import Control.Monad

newtype State s a = State { runState :: s -> (a, s) }

instance Monad (State s) where
    -- return :: a -> State s a
    return x = State (\st -> (x, st))

    -- (runState x) gets the lambda from the monadic value, and calls it with
    -- the state.  The result will be the new value and the new state.  Then
    -- we call the bound function, which returns a monadic value.

    -- (>>=) :: State s a -> (a -> State s b) -> State s b
    x >>= f = State $ \st ->
                let (y, st') = (runState x) st
                in (runState (f y)) st'

get :: State a a
get = State $ \st -> (st, st)

put :: s -> State s ()
put newState = State $ \_ -> ((), newState)

------------------------------------------------------------------------

baz :: Int -> State Int Int
baz y = do if y == 0
             then put 10
             else return ()
           x <- get
           return (x + 11)

bar :: State Int Int
bar = do put 20
         _ <- baz 0
         y <- get
         return y

foo :: (Int, Int)
foo = runState bar 0
