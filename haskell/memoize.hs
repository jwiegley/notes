{-# LANGUAGE BangPatterns #-}

import Data.Function (fix)

-- Let's define f, but make it use 'open recursion' rather than call itself directly.

f :: (Integer -> Integer) -> Integer -> Integer
f mf 0 = 0
f mf n = max n $ mf (div n 2) +
                 mf (div n 3) +
                 mf (div n 4)

f_list :: [Integer]
f_list = map (f faster_f) [0..]

faster_f :: Integer -> Integer
faster_f n = f_list !! fromIntegral n

data Tree a = Tree (Tree a) a (Tree a)
instance Functor Tree where
    fmap f (Tree l m r) = Tree (fmap f l) (f m) (fmap f r)

index :: Tree a -> Integer -> a
index (Tree _ m _) 0 = m
index (Tree l _ r) n = case (n - 1) `divMod` 2 of
    (q,0) -> index l q
    (q,1) -> index r q

nats :: Tree Integer
nats = go 0 1
    where
        go !n !s = Tree (go l s') n (go r s')
            where
                l = n + s
                r = l + s
                s' = s * 2

toList :: Tree a -> [a]
toList as = map (index as) [0..]

f_tree :: Tree Integer
f_tree = fmap (f fastest_f) nats

fastest_f :: Integer -> Integer
fastest_f = index f_tree