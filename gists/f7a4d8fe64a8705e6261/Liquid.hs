module Liquid where

import Data.List

{-@ inline isNat @-}
isNat :: Int -> Bool
isNat n = n >= 0

{-@ type Nat = { n : Int | isNat n } @-}

{-@ constant :: Nat @-}
constant :: Int
constant = 20

{-@ double :: Nat -> Nat @-}
double :: Int -> Int
double n = n * 2

{-@ foo :: { n : Int | isNat n } -> { n : Int | isNat n } @-}
foo :: Int -> Int
foo n = double constant + double n

-- what if we change constant to just be < 200?

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ type NonEmpty a = { xs : [a] | size xs > 0 } @-}

unsafeHead :: [a] -> a
unsafeHead (x:_) = x

{-@ safeHead :: NonEmpty a -> a @-}
safeHead :: [a] -> a
safeHead (x:_) = x

bar = safeHead [1,2,3]

{- @ inline quux @-}
quux :: Int -> Bool
quux = const False

{-@ example :: Nat @-}
example :: Int
example = if 10 == 9
          then (-1)
          else constant

-- BUG?
{- @ foldExample :: { x : Nat | x < 30 } @-}
foldExample :: Int
foldExample = foldl' (+) constant [constant]


{-@ type True  = {v:Bool |    Prop v  } @-}
{-@ type False = {v:Bool | not (Prop v) } @-}

{-@ type Implies P Q = {v:_ | Prop v <=> (Prop P => Prop Q)} @-}

{-@ implies :: p:Bool -> q:Bool -> Implies p q  @-}
implies False _ = True
implies _ True  = True
implies _ _     = False

data Theo = Theo Int

-- BUG?
instance Num Theo where
    x + y = x


{-@ plusComm :: _ -> _ -> True @-}
plusComm x y = (x + y) == (y + x)

{-@ plusAssoc :: _ -> _ -> _ -> True @-}
plusAssoc x y z = ((x + y) + z) == (x + (y + z))


data Foo a = Foo { getFoo :: [a] }
    deriving Eq

{-@ data Foo a = Foo {
      getFoo :: NonEmpty a
    } @-}

{-@ assume concatMap :: _ -> xs:[a] -> { ys:[b] | size xs == size ys } @-}

instance Monad Foo where
    return x = Foo [x]
    Foo xs >>= f = Foo (concatMap (getFoo . f) xs)

{- @ fooMonadLaw1 :: (a -> Foo b) -> a -> True @-}
-- fooMonadLaw1 :: Eq b => (a -> Foo b) -> a -> Bool
-- fooMonadLaw1 f x = (return x >>= f) == (f x)
