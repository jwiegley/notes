module Balance 
    () where

import qualified Data.Set as Set
import qualified Data.Map as Map

-- accountName retrieves the account name from a posting
accountName :: a -> String
accountName post = "One:Two:Three"

-- visitAccounts walk through a list of postings and returns a set of account
-- names "visited" by those postings.  This is the first step.
visitAccounts :: (a -> Bool) -> [a] -> Set.Set String
visitAccounts fn [] = Set.empty
visitAccounts fn (x:xs) 
    | fn x      = Set.insert (accountName x) $ visitAccounts fn xs
    | otherwise = visitAccounts fn xs

splitWith :: (a -> Bool) -> a -> [a]
splitWith _ [] = []
splitWith f x = let (pre, suf) = break f x
                in pre : case suf of
                           (y:ys) -> splitWith f ys
                           _      -> []

--data AccountMap = EmptyMap | AccountMap String AccountMap deriving (Show, Read)

--fileAccountString :: AccountMap -> String -> AccountMap
--fileAccountString acc [] = acc
--fileAccountString acc s = fileAccountString' acc $ splitAt (==':') s
--    where fileAccountString' _ [] = EmptyMap
--          fileAccountString' acc (x:xs)
--              = Map.insert x (fileAccountString' map xs) acc
--              -- jww (2009-03-12): What is the equivalent of short-circuit ||?
--              where map = Map.lookup x acc || EmptyMap

--buildAccountMap :: [String] -> AccountMap
--buildAccountMap [] = EmptyMap
--buildAccountMap strs = foldl fileAccountString EmptyMap strs

--formatAccounts :: (String -> Bool), [String] -> [String]
