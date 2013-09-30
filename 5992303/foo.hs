import Data.Traversable

f :: Int -> IO String
f = return . show

g :: Int -> IO (Maybe Int)
g = return . Just

main :: IO ()
main = do
    x <- g 10
    print x

    y <- sequenceA . fmap f =<< g 10
    print y