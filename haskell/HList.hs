module HList where

data HList (ts :: [Type]) where
  Nil :: HList '[]
  Cons :: x -> HList xs -> HList (x : xs)

class Member (x :: Type) (xs :: [Type]) where
  element :: HList xs -> x

instance Member x (x : xs) where
  element (Cons x _) = x

instance Member x (y : xs) where
  element (Cons _ xs) = element xs

