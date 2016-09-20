module Felko where

data FailableState e s a = State (s -> (a, s)) | Failed e

instance Monad (FailableState e s) where
    Failed err >>= _ = Failed err
    x >>= f = case evalFailableState x s of
            Right x  -> State $ \ s -> f x
            Left err -> Failed err
