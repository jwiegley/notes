{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE StandaloneDeriving #-}

module ParaList where

import           Control.Applicative
import           Control.Monad
import           Data.List           (tails)
import           Data.Set            (Set)
import qualified Data.Set            as S

-- This type courtesy of Oleg: http://okmij.org/ftp/Haskell/set-monad.html
data SetM a where
  SMOrd :: Ord a => Set a -> SetM a
  SMAny :: [a] -> SetM a

instance Functor SetM where
  fmap f = SMAny . fmap f . toList

instance Applicative SetM where
  pure x  = SMAny [x]
  f <*> s = SMAny (toList f <*> toList s)

instance Monad SetM where
  return = pure
  m >>= f = collect . fmap f $ toList m

deriving instance Foldable SetM

instance Traversable SetM where
  traverse f s = SMAny <$> traverse f (toList s)

toList :: SetM a -> [a]
toList (SMOrd x) = S.toList x
toList (SMAny x) = x

fromList :: [a] -> SetM a
fromList = SMAny

collect :: [SetM a] -> SetM a
collect []              = SMAny []
collect [x            ] = x
collect ((SMOrd x) : t) = case collect t of
  SMOrd y -> SMOrd (S.union x y)
  SMAny y -> SMOrd (S.union x (S.fromList y))
collect ((SMAny x) : t) = case collect t of
  SMOrd y -> SMOrd (S.union y (S.fromList x))
  SMAny y -> SMAny (x ++ y)

runSetM :: Ord a => SetM a -> Set a
runSetM (SMOrd x) = x
runSetM (SMAny x) = S.fromList x

instance Alternative SetM where
  empty = SMAny []
  SMAny x <|> SMAny y = SMAny (x ++ y)
  SMAny x <|> SMOrd y = SMOrd (S.union y (S.fromList x))
  SMOrd x <|> SMAny y = SMOrd (S.union x (S.fromList y))
  SMOrd x <|> SMOrd y = SMOrd (S.union x y)

instance MonadPlus SetM where
  mzero = empty
  mplus = (<|>)

choose :: Ord a => [a] -> SetM a
choose x = SMOrd (S.fromList x)

splits :: [a] -> [(a, [a])]
splits = zip <*> tail . tails

foo :: Set Int
foo = runSetM $ do
  (x, xs) <- choose $ splits [1 .. 10]
  guard (x > (5 :: Int))
  y <- choose xs
  guard (x < y)
  return x                      -- return x's that pass
