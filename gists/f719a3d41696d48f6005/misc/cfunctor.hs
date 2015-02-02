{-# LANGUAGE MultiParamTypeClasses #-}

data Foo a = Foo a deriving Show
data Bar a = Bar a deriving Show

class Iso a b where
  convert :: a -> b
  invert :: b -> a

instance Iso (Foo a) (Bar a) where
  convert (Foo x) = Bar x
  invert (Bar x)  = Foo x

main = do
  print (convert (Foo (10 :: Int)) :: Bar Int)