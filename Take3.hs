module Main where

import Pipes
import Pipes.Prelude as P
import Data.Maybe

data Foo = Foo

foo :: Foo -> IO (Foo, Maybe Int)
foo = undefined

fooProducer :: Foo -> Producer (Maybe Int) IO ()
fooProducer x = do
    (x', y) <- liftIO $ foo x
    yield y
    fooProducer x'

main :: IO ()
main = do
    xs <- P.toListM $ fooProducer Foo >-> P.filter isJust >-> P.take 3
    Prelude.print xs
