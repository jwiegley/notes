f :: (a -> b) -> a -> b
f g = g

fails :: IO ()
fails = do f putStrLn "Hello"
