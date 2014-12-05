module Swift where

data FooArgs = FooArgs
data Result = Result

untilRight :: (e -> Either e a) -> e -> a
untilRight f = go where
    go x = case f x of
        Left y  -> go y
        Right y -> y

swift :: (FooArgs -> Either FooArgs Result) -> FooArgs -> Result
swift = untilRight
