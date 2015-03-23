{-# LANGUAGE RankNTypes #-}

module EndoFunctor where

import Data.Monoid

newtype DList a = DList { getDList :: Endo [a] }

data Coyoneda f a = forall r. Coyoneda (r -> a) (f r)

instance Functor (Coyoneda f) where
    fmap f (Coyoneda g z) = Coyoneda (f . g) z

liftCoyoneda :: f a -> Coyoneda f a
liftCoyoneda = Coyoneda id

lowerCoyoneda :: Functor f => Coyoneda f a -> f a
lowerCoyoneda (Coyoneda f k) = fmap f k

lowerDList :: Coyoneda DList a -> [a]
lowerDList (Coyoneda f (DList x)) = map f (appEndo x [])

main :: IO ()
main = do
    let l0 = DList $ Endo ((:) "Hello") <> Endo ((:) " ") <> Endo ((:) "World")
    let l1 = liftCoyoneda l0
    let l2 = fmap (++ ("..." :: String)) l1
    print $ concat $ lowerDList l2
