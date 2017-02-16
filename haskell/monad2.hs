module Main where

import Control.Applicative
import Data.Monoid
import Data.Traversable
import Data.Foldable

-- Say I define a Binary Tree data structure

data Tree a = Empty | Leaf a | Node (Tree a) a (Tree a)

-- I want the tree to be traversable.  I could do this by creating a custom
-- traversal function, but it's more natural if I define what it means to map
-- over the tree by creating a Functor for Trees:

instance Functor Tree where
  fmap f Empty = Empty

  -- Mapping f over a leaf node means call f on the value at the leaf, and
  -- returning a new leaf with the resulting value.
  fmap f (Leaf a) = Leaf (f a)

  -- Mapping f over a branch node means continuing the map down both sides of
  -- the tree from the branch, returning a new branch with the new left and
  -- right sides.
  fmap f (Node l k r) = Node (fmap f l) (f k) (fmap f r)

-- If I fmap over a tree now, I get a back a new tree where the operation has
-- been applied to every node.  fmap id x = x.

-- Now let's say I want to sum all the integers in a tree of ints.  I can use
-- mapAccumL to do a map and fold at the same time.  I just have to make my
-- tree a Traversable thing, which is identical in form to a Functor, but uses
-- applicative style:

instance Traversable Tree where
  traverse f Empty = pure Empty
  traverse f (Leaf x) = Leaf <$> f x
  traverse f (Node l k r) = Node <$> traverse f l <*> f k <*> traverse f r

-- I also need to make the Tree type foldable:

instance Foldable Tree where
  foldMap f Empty = mempty
  foldMap f (Leaf x) = f x
  foldMap f (Node l k r) = foldMap f l `mappend` f k `mappend` foldMap f r

--       5
--      / \
--     3   8
--    / \
--   2   4
foo :: Tree Int
foo = Node (Node (Leaf 2) 3 (Leaf 4)) 5 (Leaf 8)

treesum :: IO ()
treesum = do
  putStrLn $ show $ fst $ mapAccumL (\acc x -> (acc + x, x)) 0 foo

-- => 22

-- As we can see, adding my Tree type to a type class exposes a functional
-- interface, allowing other Haskell libraries to manipulate it.
--
--   Functor      mapping over the tree
--   Traversable  same as Functor, in applicative style
--   Foldable     allows folding of values during traversal

-- What if we made a Tree Monad, what would that buy us?  So far, functors
-- allow us traverse the tree, creating a new tree with value transformations
-- at each node.  What a monad does is allow us to perform *structural
-- substitutions* at each node.  That is, instead of transforming the values
-- (the integers) in the tree, we can transform the tree's structure (the
-- nodes), but *based on the values*.
--
-- That is, fmap f x, where x is a Tree, applies f to every value in the tree,
-- where values are either (Leaf x) or (Node _ x _).  f must return another
-- value of the same type.
--
-- With a monad, x >>= f applies f to every value in the tree (the Int's), but
-- each call of f must return a new *Tree*, not a new Int as with fmap.  So,
-- if f x returns Leaf x for every value in the tree, the resulting tree will
-- have the same structure, _because the Monad is doing the job of patching
-- together these new trees during the traversal_.
-- 
-- Correspondingly, this is exactly what the List Monad does when you bind
-- functions over it: since each function must return a new list, and not a
-- new value.  Yet the result of such a bind is a list, rather than a list of
-- lists.  This is because the functionality of List's >>= operator is that it
-- splices together all the new lists returned from the bound function.  Thus,
-- binding `id' over [1, 2, 3] internally produces [1], [2], [3], which are
-- then joined together to form [1, 2, 3].  The power of the Monad abstraction
-- is that a function you bind to a list can at any time return a list of more
-- than one element, and these are seamlessly joined into the resulting list.

-- This allows me to, say, delete nodes from the tree that have a value less
-- than 5.  See below for the use of `prunedTree'.

makeNode Empty Empty r = r
makeNode l Empty Empty = l

makeNode l Empty r = makeNode Empty l r

makeNode l (Leaf x) r = Node l x r

makeNode l (Node l' x r') r =
  Node (node' l l') x (node' r r')
  where
    node' Empty i = i
    node' i Empty = i

    node' l@(Leaf i) (Leaf j) = Node l j Empty

    node' l@(Node _ i _) (Leaf j) = Node l j Empty
    node' (Leaf i) r@(Node _ j _) = Node Empty i r

    node' l@(Node _ i _) r@(Node _ j _) = makeNode Empty l r

instance Monad Tree where
  return x = Leaf x
  Empty >>= f = Empty
  Leaf x >>= f = f x
  Node l x r >>= f = makeNode (l >>= f) (f x) (r >>= f)

deleteNodeIf :: (Int -> Bool) -> Int -> Tree Int
deleteNodeIf f x = if f x then Empty else Leaf x

prunedTree :: Tree Int -> Tree Int
prunedTree x = x >>= deleteNodeIf (<5)

treemod :: IO ()
treemod = do
  putStrLn $ show $ fst $ mapAccumL (\acc x -> (acc + x, x)) 0 $ prunedTree foo

truth x = x >>= Leaf
