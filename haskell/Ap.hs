module Ap where

import Control.Applicative hiding ((<**>))

infixl 8 <$$>
(<$$>) :: Applicative f => (a -> b -> c) -> f ((a -> b -> c) -> c) -> f c
f <$$> x = x <*> pure f

infixr 7 <**>
(<**>) :: Monad f => f a -> f b -> f ((a -> b -> c) -> c)
f <**> x = do
    a <- f
    b <- x
    return $ \k -> k a b

main :: IO ()
main = do
    print =<< (,,) <$> return 4 <*> return 5 <*> return 6
    print =<< ((,,) <$> return (4 :: Int) <**> return (5 :: Int) <**> return (6 :: Int))
