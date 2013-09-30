module Main where

import Orc

speculate :: Eq b => (a -> Orc b) -> (b -> Orc c) -> a -> (a -> b) -> Orc c
speculate f g x guess = do
    let w = guess x
    z <- eagerly (g w)
    y <- f x
    if y == w
        then z
        else g y

main = do
    printOrc $ speculate foo bar 1 (const 2)
    printOrc $ speculate foo bar 1 (const 11)
  where
    foo x = do
        liftIO $ putStrLn $ "in foo(" ++ show x ++ ")..."
        delay 10
        return $ x + 10

    bar x = do
        liftIO $ putStrLn $ "in bar(" ++ show x ++ ")..."
        delay 10
        return $ x + 33
