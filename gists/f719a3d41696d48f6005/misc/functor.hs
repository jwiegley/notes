module FunctorExample where

import Data.List
import Data.Foldable as DF
import Data.Monoid

data Tree a = Node (Tree a) (Tree a) | Leaf a | Empty
            deriving Show

instance Functor Tree where
  fmap _ Empty = Empty
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Node x y) = Node (fmap f x) (fmap f y)
  -- jww (2012-08-13): This definition of fmap breaks the first law!
  -- fmap f (Node x y) = Node (fmap f y) (fmap f x)

instance Foldable Tree where
  foldMap _ Empty = mempty
  foldMap f (Leaf a) = f a
  foldMap f (Node x y) = foldMap f x `mappend` foldMap f y

sampleTree :: Tree Int
sampleTree = (Node (Node (Leaf 1) Empty)
                   (Node (Leaf 2)
                         (Node (Leaf 3) (Leaf 4))))

getTreeList :: Tree a -> [a]
getTreeList = DF.foldr (:) []

main = do
  let args = getArgs
  args <- getArgs
  putStrLn args

main = getArgs >>= putStrLn

main = putStrLn =<< getArgs

main :: IO ()
main = do
  -- It shouldn't matter whether we fmap id over the "list from the tree", or
  -- if we fmap id over the tree and then turn it into a list.  Both lists
  -- must be identical according to the first law
  if fmap id (getTreeList sampleTree) == getTreeList (fmap id sampleTree)
    then print "Homomorphism was observed"
    else print "First functor law violated!"

  -- Since the tree was in sorted order, the list of elements should match the
  -- sorted list of elements
  let treeList' = getTreeList (fmap id sampleTree)
  if treeList' == sort treeList'
    then print "Homomorphism was observed"
    else print "First functor law violated!"

  -- And likewise with list of elements derived from an id mapping of the tree
  -- should match the sorted list of elements
  let treeList'' = fmap id (getTreeList sampleTree)
  if treeList'' == sort treeList''
    then print "Homomorphism was observed"
    else print "First functor law violated!"

-- functor.hs ends here
