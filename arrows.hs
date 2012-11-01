{-# LANGUAGE Arrows #-}

import Control.Category
import Control.Arrow
import Control.Monad
import Prelude hiding (id, (.))
import System.IO.Unsafe

data IOArrow a b = IOArrow { runIOArrow :: a -> IO b }

instance Category IOArrow where
  id = IOArrow return
  IOArrow f . IOArrow g = IOArrow $ f <=< g

instance Arrow IOArrow where
  arr f = IOArrow $ return . f
  first (IOArrow f) = IOArrow $ \(a, c) -> do
    x <- f a
    return (x, c)

foo :: Int -> String
foo = show

bar :: String -> IO Int
bar = return . read

arrowUser :: Arrow a => a String String -> a String String
arrowUser f = proc x -> do
  y <- f -< x
  returnA -< y

main :: IO ()
main = do
  let h =    arr (++ "!")
          <<< arr foo
          <<< Kleisli bar
          <<< arr id
  result <- runKleisli (arrowUser h) "123"
  putStrLn result

arrowUser' :: (String -> String) -> String -> String
arrowUser' f x = f x

main' :: IO ()
main' = do
  let h      = (++ "!") . foo . unsafePerformIO . bar . id
      result = arrowUser' h "123"
  putStrLn result
