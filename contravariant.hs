module Main where

data Predicate a = Predicate { runPredicate :: a -> Bool }

class Contravariant f where
  cmap :: (a -> b) -> f b -> f a

instance Contravariant Predicate where
  cmap f x = Predicate $ \a -> (runPredicate x) (f a)

startsWith1 :: String -> Bool
startsWith1 str = head str == '1'

main :: IO ()
main = do
  print $ runPredicate (cmap (show :: Int -> String) (Predicate startsWith1)) 10
