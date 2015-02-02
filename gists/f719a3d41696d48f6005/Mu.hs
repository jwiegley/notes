{-# LANGUAGE DeriveFunctor #-}

module Mu where

data NatF a = Z | S a deriving (Functor, Show)

newtype Fix (f :: * -> *) = Fix { outF :: f (Fix f) }

type FixNat = Fix NatF

cata :: Functor f => (f a -> a) -> Fix f -> a
cata k = k . fmap (cata k) . outF

fixToInt :: FixNat -> Integer
fixToInt (Fix Z) = 0
fixToInt (Fix (S n)) = 1 + fixToInt n

newtype Mu (f :: * -> *) = Mu { outMu :: forall a. (f a -> a) -> a }

type MuNat = Mu NatF

cataMu :: Functor f => (f a -> a) -> Mu f -> a
cataMu k x = outMu x k

muToInt :: MuNat -> Integer
muToInt (Mu f) = f phi
  where
    phi Z = 0
    phi (S n) = 1 + n

zero :: MuNat
zero = Mu $ \f -> f Z

one :: MuNat
one = Mu $ \f -> f (S (f Z))

data Nu (f :: * -> *) = forall a. Nu a (a -> f a)

type NuNat = Nu NatF

anaNu :: Functor f => (a -> f a) -> a -> Nu f
anaNu k x = Nu x k

intToNu :: Integer -> NuNat
intToNu n = Nu n (S . succ)

main :: IO ()
main = do
    let x = Fix (S (Fix (S (Fix (S (Fix Z))))))
        -- ^ Fix builds a "syntax tree" representing the data, which can later
        --   be evaluated by traversal using 'cata'.

        y = Mu (\f -> f (S (f (S (f (S (f Z)))))))
        -- ^ Mu builds a CPS transform of over the data, using a "constructor"
        --   function.  This permits evualation by choice of constructor.

    -- As should be clear from the definitions of x and y:
    --   x == outMu y Fix
    -- and:
    --   y == Mu (`cata` x)

    print $ fixToInt x
    print $ fixToInt (outMu y Fix)

    print $ muToInt  y
    print $ muToInt  (Mu (`cata` x))
