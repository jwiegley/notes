{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Hetero where

import Control.Lens
import Data.Functor.Adjunction

data Hetero f g a b = Hetero (a -> g b) (f a -> b)

instance Functor g => Functor (Hetero f g a) where
    fmap h (Hetero j k) = Hetero (fmap h . j) (h . k)

instance Adjunction f g => Profunctor (Hetero f g) where
    dimap h i (Hetero j k) = Hetero (fmap i . lmap h j) (rmap i k . fmap h)

hetero :: (s -> g a) -> (f b -> t) -> Iso s t (g a) (f b)
hetero f g = iso f g

-- type State s a = Hetero ((,) s) ((->) s) a a
-- -- type State s a = Hetero (a -> s -> a) ((s,a) -> a)

-- state :: Hetero ((,) s) ((->) s) a a
-- state = Hetero const snd

-- get ∷ State s s
-- get s = (s,s)

-- put ∷ s → State s ()
-- put s _ = (s,())

-- runState ∷ State s a → s → (s,a)
-- runState (Hetero j k) s = 

-- evalState ∷ State s a → s → a
-- evalState = (snd .) . runState

-- execState ∷ State s a → s → s
-- execState = (fst .) . runState

-- foo ∷ Num a ⇒ State a a
-- foo = runState (put 10 >> get)

-- main :: IO ()
-- main = do
--     let x = state
--     print "Hello"
