{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Fin where

import GHC.TypeLits

data Fin :: Nat -> * where
    F1 :: Fin (n + 1)
    FS :: Fin n -> Fin (n + 1)

toInt :: Fin n -> Int
toInt F1 = 0
toInt (FS n) = 1 + toInt n

instance Show (Fin n) where
    show = show . toInt

main = do
    print $ (FS (FS (FS F1)) :: Fin 10)
    print $ (FS (FS (FS F1)) :: Fin 5)
    print $ (FS (FS (FS F1)) :: Fin 4)
    print $ (FS (FS (FS F1)) :: Fin 2)
    print $ (FS (FS (FS F1)) :: Fin 3)
