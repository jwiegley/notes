{-# LANGUAGE Arrows #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Control.Arrow.Free where

import Control.Arrow
import Control.Category
import Data.Function hiding ((.), id)
import Data.Profunctor
import Prelude hiding ((.), id)

infixr :-

-- | This definition of 'FreeA' is from Dan Piponi:
--   http://blog.sigfpe.com/2017/01/building-free-arrows-from-components.html

data FreeA p a b where
    PureP :: (a -> b) -> FreeA p a b
    LoopP  :: FreeA p (a, d) (b, d) -> FreeA p a b
    (:-)  :: p a x -> FreeA p x b -> FreeA p a b

instance Show (FreeA p a b) where
    show (PureP _) = "PureP f"
    show (LoopP g) = "LoopP (" ++ show g ++ ")"
    show (_ :- g)  = "f :- " ++ show g

nil :: Profunctor p => FreeA p a a
nil = PureP id

instance Profunctor b => Profunctor (FreeA b) where
    lmap f (PureP g) = PureP (g . f)
    lmap f (LoopP g) = LoopP (lmap (first f) g)
    lmap f (g :- h)  = lmap f g :- h

    rmap f (PureP g) = PureP (f . g)
    rmap f (LoopP g) = LoopP (rmap (first f) g)
    rmap f (g :- h)  = g :- rmap f h

instance Strong p => Strong (FreeA p) where
    first' (PureP f) = PureP (first' f)
    first' (LoopP f) = LoopP (arr (\((b, d), c) -> ((b, c), d)) <<< first' f <<<
                              arr (\((a, d), c) -> ((a, c), d)))
    first' (f :- g)  = first' f :- first' g

instance (Profunctor p, Strong p) => Category (FreeA p) where
    id = PureP id
    g . PureP f  = lmap f g
    g . LoopP f  = LoopP (first' g . f)
    k . (g :- h) = g :- (k . h)

instance (Profunctor p, Strong p) => Arrow (FreeA p) where
    arr = PureP
    first = first'

instance (Profunctor p, Strong p) => ArrowLoop (FreeA p) where
    loop = LoopP

foldFreeA :: (Profunctor p, Arrow a, ArrowLoop a)
          => (forall x y. p x y -> a x y) -> FreeA p b c -> a b c
foldFreeA _ (PureP g) = arr g
foldFreeA f (LoopP x) = loop (foldFreeA f x)
foldFreeA f (g :- h)  = foldFreeA f h . f g

newtype SF a b = SF { getSF :: FreeA (->) [a] [b] }

instance Category SF where
    id = SF id
    SF f . SF g = SF (f . g)

instance Arrow SF where
    arr = SF . arr . map
    first (SF f) = SF (arr unzip >>> first f >>> arr (uncurry zip))

instance ArrowLoop SF where
    loop (SF f) = SF $ loop (arr unzip <<< f <<< arr (uncurry ((. stream) . zip)))

stream :: [a] -> [a]
stream ~(x:xs) = x:stream xs

delay :: a -> SF a a
delay x = SF $ arr (x:)

mul :: Arrow arr => arr (Integer, Integer) Integer
mul = arr (uncurry (*))

facSF :: SF Integer Integer
facSF = loop (mul >>> (arr id &&& delay 1))

fac :: Integer -> Integer
fac x = foldFreeA id (getSF facSF) [1..x] !! fromInteger (x - 1)

{- EXAMPLE -}

data Component a b = Load ((a, Int) -> b)
                   | Store (a -> (b, Int))
                   | Inc (a -> b)

instance Profunctor Component where
    lmap f (Load g)  = Load $ \(a, s) -> g (f a, s)
    lmap f (Store g) = Store (g . f)
    lmap f (Inc g)   = Inc (g . f)

    rmap f (Load g)  = Load (f . g)
    rmap f (Store g) = Store $ \a ->
        let (b, t) = g a in  (f b, t)
    rmap f (Inc g)   = Inc (f . g)

instance Strong Component where
    first' (Load g)  = Load $ \((a, x), s) -> (g (a, s), x)
    first' (Store g) = Store $ \(a, x) ->
        let (b, t) = g a in  ((b, x), t)
    first' (Inc g)   = Inc (first' g)

add :: Num a => FreeA Component (a, a) a
add = PureP $ uncurry (+)

load :: FreeA Component () Int
load = Load snd :- nil

store :: FreeA Component Int ()
store = Store (\a -> ((), a)) :- nil

inc :: FreeA Component a a
inc = Inc id :- nil

test :: FreeA Component () ()
test = proc () -> do
    () <- inc   -< ()
    a  <- load  -< ()
    b  <- load  -< ()
    c  <- add   -< (a, b)
    () <- store -< c
    returnA -< ()

newtype Circuit s a b = C { runC :: (a, s) -> (b, s) }

instance Category (Circuit s) where
    id = C id
    C f . C g = C (f . g)

instance Arrow (Circuit s) where
    arr = C . first
    first (C g) = C $ \((a, x), s) ->
        let (b, t) = g (a, s)
        in  ((b, x), t)

instance ArrowLoop (Circuit s) where
    loop = undefined

exec :: Component a b -> Circuit Int a b
exec (Load g)  = C $ \(a, s) -> (g (a, s), s)
exec (Store g) = C $ g . fst
exec (Inc g)   = C $ g *** succ

main :: IO ()
main = print $ runC (foldFreeA exec test) ((), 10)
