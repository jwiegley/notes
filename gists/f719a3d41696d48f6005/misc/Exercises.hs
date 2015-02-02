{-
The 'Scala exercises for beginners' set rules about what you were not permitted to use.
This is because you were permitted to use some functions, but not others. This led to
some amount of confusion (sorry). Instead, this time, I will define my own data types. 
One is equivalent to Haskell's list [], although without the syntactic support and the
other is the set of natural numbers (0 onward). I will also predefine some useful
functions that you might consider using to solve each problem. That way, I needn't set 
any rules; you are very much free to do what you want (Although, converting between 
this type and [] is considered cheating, as you might expect ;).

I will consider converting the Scala exercises to use a similar strategy in a second 
revision to prevent this confusion.

TOTAL marks:    /66
-}

module Exercises where

import Prelude hiding (sum, length, map, filter, maximum, reverse, succ, pred)

-- The custom list type
data List t = Nil | Cons t (List t)

instance (Show t) => Show (List t) where
  show = show . toList
    where
    -- unfoldr, but let's not import Data.List
    toList Nil = []
    toList (Cons h t) = h : toList t

-- the custom numeric type
data Natural = Zero | Succ Natural
one = Succ Zero
two = Succ one

instance Show Natural where
  show = show . toInt
    where
    toInt Zero = 0
    toInt (Succ x) = 1 + toInt x

-- functions over Natural that you may consider using
succ :: Natural -> Natural
succ = Succ

pred :: Natural -> Natural
pred Zero = error "bzzt. Zero has no predecessor in naturals"
pred (Succ x) = x

-- functions over List that you may consider using
foldRight :: (a -> b -> b) -> b -> List a -> b
foldRight _ b Nil = b
foldRight f b (Cons h t) = f h (foldRight f b t)

foldLeft :: (b -> a -> b) -> b -> List a -> b
foldLeft _ b Nil = b
foldLeft f b (Cons h t) = let b' = f b h in b' `seq` foldLeft f b' t

reduceRight :: (a -> a -> a) -> List a -> a
reduceRight _ Nil = error "bzzt. reduceRight on empty list"
reduceRight f (Cons h t) = foldRight f h t

reduceLeft :: (a -> a -> a) -> List a -> a
reduceLeft _ Nil = error "bzzt. reduceLeft on empty list"
reduceLeft f (Cons h t) = foldLeft f h t

unfold :: (b -> Maybe (a, b)) -> b -> List a
unfold f b = case f b of Just (a, b') -> a `Cons` unfold f b'
                         Nothing -> Nil

-- Exercises

-- Exercise 1
-- Relative Difficulty: 1
-- Correctness: 2.0 marks
-- Performance: 0.5 mark
-- Elegance: 0.5 marks
-- Total: 3
add :: Natural -> Natural -> Natural
add = error "todo"

-- Exercise 2
-- Relative Difficulty: 2
-- Correctness: 2.5 marks
-- Performance: 1 mark
-- Elegance: 0.5 marks
-- Total: 4
sum :: List Int -> Int
sum = error "todo"

-- Exercise 3
-- Relative Difficulty: 2
-- Correctness: 2.5 marks
-- Performance: 1 mark
-- Elegance: 0.5 marks
-- Total: 4
length :: List a -> Int
length = error "todo"

-- Exercise 4
-- Relative Difficulty: 5
-- Correctness: 4.5 marks
-- Performance: 1.0 mark
-- Elegance: 1.5 marks
-- Total: 7
map :: (a -> b) -> List a -> List b
map = error "todo"

-- Exercise 5
-- Relative Difficulty: 5
-- Correctness: 4.5 marks
-- Performance: 1.5 marks
-- Elegance: 1 mark
-- Total: 7
filter :: (a -> Bool) -> List a -> List a
filter = error "todo"

-- Exercise 6
-- Relative Difficulty: 5
-- Correctness: 4.5 marks
-- Performance: 1.5 marks
-- Elegance: 1 mark
-- Total: 7
append :: List a -> List a -> List a
append = error "todo"

-- Exercise 7
-- Relative Difficulty: 5
-- Correctness: 4.5 marks
-- Performance: 1.5 marks
-- Elegance: 1 mark
-- Total: 7
flatten :: List (List a) -> List a
flatten = error "todo"

-- Exercise 8
-- Relative Difficulty: 7
-- Correctness: 5.0 marks
-- Performance: 1.5 marks
-- Elegance: 1.5 mark
-- Total: 8
flatMap :: List a -> (a -> List b) -> List b
flatMap = error "todo"

-- Exercise 9
-- Relative Difficulty: 8
-- Correctness: 3.5 marks
-- Performance: 3.0 marks
-- Elegance: 2.5 marks
-- Total: 9
maximum :: List Int -> Int
maximum = error "todo"

-- Exercise 10
-- Relative Difficulty: 10
-- Correctness: 5.0 marks
-- Performance: 2.5 marks
-- Elegance: 2.5 marks
-- Total: 10
reverse :: List a -> List a
reverse = error "todo"

