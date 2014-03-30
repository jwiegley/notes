{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Combining where

import Control.Applicative
import Control.Arrow
import Control.Lens
import Control.Lens.Internal
import Control.Lens.Internal.Context
import Control.Monad
import Data.Bitraversable
import Data.Functor

{-

newtype Pretext p a b t = Pretext (Functor f => p a (f b) -> f t)
type Pretext' p a = Pretext p a a
type LensLike f s t a b = (a -> f b) -> s -> f t
type LensLike' f s a = LensLike f s s a a

LensLike' (Pretext' p a) s a
LensLike (Pretext p a a) s s a a
(a -> Pretext p a a a) -> s -> Pretext p a a s

type ALens s t a b = LensLike (Pretext (->) a b) s t a b
type ALens' s a = ALens s s a a

-}

-- pairing :: ALens' s a -> ALens' s a'-> Lens' s (a, a')
-- pairing x x' =
--     lens (\s -> (s ^# x, s ^# x'))
--          (\s (a, a') -> s & x #~ a & x' #~ a')

pairing :: Functor f
        => LensLike' (PretextT' (->) f a) s a
        -> LensLike' (PretextT' (->) f a') s a'
        -> LensLike' f s (a, a')
pairing l r f s = do
    x <- l sell s
    y <- r sell s
    contramap f (x *** y)
  --   let h = fmap (r sell) $ l sell s
  --   in runPretextT (merge h) f
  -- where
  --   -- p a (f b) -> f (p a' (f b) -> f t)
  --   --  -into-
  --   -- p (a, a') (f b) -> f t
  --   merge :: PretextT' (->) f a (PretextT' (->) f a' s)
  --         -> PretextT' (->) f (a, a') s
  --   merge (PretextT k) = PretextT $ \g -> k undefined

main :: IO ()
main = do
    print $ (1,2,3,4) ^. pairing _2 _4
    print $ (1,2,3,4) ^. pairing (to (\(_, x, _, _) -> x))
                                 (to (\(_, _, _, x) -> x))
    print $ (1,2,3,4)  & pairing _2 _4 .~ (10, 20)
