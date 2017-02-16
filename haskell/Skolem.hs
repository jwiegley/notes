{-# LANGUAGE RankNTypes #-}

module Skolem where

newtype Scope s a = Scope a

instance Functor (Scope s) where
    fmap f (Scope x) = Scope (f x)

instance Monad (Scope s) where
    return = Scope
    Scope m >>= f = f m

data Var s a = Var { getVar :: a } deriving Show

runScope :: (forall s. Scope s a) -> a
runScope (Scope x) = x

makeVar :: Int -> Scope s (Var s Int)
makeVar = Scope . Var

readVar :: Var s Int -> Scope s Int
readVar = Scope . getVar

main :: IO ()
main = do
    print $ runScope $ do
        x <- makeVar 100
        readVar x
    let x = runScope $ makeVar 100 :: Var s Int
    print (getVar x)
