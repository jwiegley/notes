{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module LZip where

import Control.Monad.State

data Zipper a = Zip [a] [a]

data TZipper a = TLeaf [a] | TBranch (TZipper a) (TZipper a)

-- Consider the list [1,2,3,4]; a zipper over the sublist [2,3] would be:
--
example :: TZipper Int
example = TBranch (TLeaf [1]) (TBranch (TLeaf []) (TLeaf [4]))

-- With this type, the hole still has a definite shape.
holeLength :: TZipper a -> Int
holeLength (TLeaf _) = 0
holeLength (TBranch xs ys) = 1 + holeLength xs + holeLength ys

-- And we can only reconstitute it with a new sublist of that shape.
fill :: TZipper a -> [a] -> [a]
fill = evalState . go
  where
    go (TLeaf xs) = return xs
    go (TBranch xs ys) = do
        pre <- go xs
        fmap (pre ++) $ get >>= \case
            [] -> go ys
            r:rs -> do
                put rs
                (r:) <$> go ys

-- If we assume the TZipper only references a single, contiguous sublist,
-- however, it can be any shape.
fillContig :: TZipper a -> [a] -> [a]
fillContig (TLeaf xs) _ = xs
fillContig (TBranch xs zs) [] = fill xs [] ++ fill zs []
fillContig (TBranch xs zs) (y : ys) = fill xs [] ++ y : fill zs ys
