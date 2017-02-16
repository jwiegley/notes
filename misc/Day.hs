{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Day where

import Control.Monad.Free
import Control.Comonad.Cofree

data AdderF k =
    Add Int (Bool -> k)
  | Clear k
  | Total (Int -> k)
  deriving Functor

type Adder a = Free AdderF a

data CoAdderF k = CoAdderF {
    addH   :: Int -> (Bool, k)
  , clearH :: k
  , totalH :: (Int, k)
  }
  deriving Functor

type Limit = Int
type Count = Int

type CoAdder a = Cofree CoAdderF a

mkCoAdder :: Limit -> Count -> CoAdder (Limit, Count)
mkCoAdder limit count = coiter next start
  where
    next w = CoAdderF (coAdd w) (coClear w) (coTotal w)
    start = (limit, count)

coClear :: (Limit, Count) -> (Limit, Count)
coClear (limit, _count) = (limit, 0)

coTotal :: (Limit, Count) -> (Int, (Limit, Count))
coTotal (limit, count) = (count, (limit, count))

coAdd :: (Limit, Count) -> Int -> (Bool, (Limit, Count))
coAdd (limit, count) x = (test, (limit, next))
  where
    count' = count + x
    test = count' <= limit
    next = if test then count' else count

add :: Int -> Adder Bool
add x = liftF $ Add x id

clear :: Adder ()
clear = liftF $ Clear ()

total :: Adder Int
total = liftF $ Total id

data Day f g a = forall b c. Day (b -> c -> a) (f b) (g c)

type Algebra f a = f a -> a

class (Functor f, Functor g) => Dual f g where
    zap :: Algebra (Day f g) r

instance Dual ((->) a) ((,) a) where
    zap (Day p f (a, b)) = p (f a) b

instance Dual ((,) a) ((->) a) where
    zap (Day p (a, b) g) = p b (g a)

instance Dual f g => Dual (Cofree f) (Free g) where
    zap (Day p (a :< _ ) (Pure x))  = p a x
    zap (Day p (_ :< fs) (Free gs)) =
        zap $ Day (\a b -> zap $ Day p a b) fs gs

instance Dual CoAdderF AdderF where
    zap (Day f (CoAdderF a _ _) (Add x k)) = zap $ Day f (a x) k
    zap (Day f (CoAdderF _ c _) (Clear k)) = f c k
    zap (Day f (CoAdderF _ _ t) (Total k)) = zap $ Day f t k

runLimit :: CoAdder a -> Int
runLimit w = zap $ Day (\_ b -> b) w $ do
    add 1
    add 2
    total
