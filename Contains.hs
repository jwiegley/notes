{-# LANGUAGE DataKinds #-}

module Contains where

import Data.List

data Contains a = Contains
    { whereAt :: !Int
    , elemens :: [a]
    }
    deriving Show

fromList :: (a -> Bool) -> [a] -> Maybe (Contains a)
fromList p xs = case findIndex p xs of
    Nothing -> Nothing
    Just n  -> Just (Contains n xs)

toList :: Contains a -> [a]
toList (Contains _ xs) = xs

main :: IO ()
main = undefined
