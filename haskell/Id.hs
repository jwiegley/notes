module Id where

import Data.IORef

foo :: Functor f => f Int -> Int -> f Int
foo val num = fmap (\x -> fromIntegral (x * num)) val

main :: IO ()
main = do
    v <- newIORef 25
    modifyIORef v (foo id 10)
    print =<< readIORef v
