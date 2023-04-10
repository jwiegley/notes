{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TemplateHaskell #-}

module StateLens where

import Control.Lens
import Control.Monad.State
import Data.Int
import Data.Time.Clock.System

data D = D {
  _foo :: Int,
  _baz :: Int
  }

makeLenses ''D

func :: State D ()
func = id %= ((foo %~ bar) . (baz .~ quux))
  where
    bar :: Int -> Int
    bar = (+1)

    quux :: Int
    quux = 20

func' :: State D ()
func' = id %= \s -> s & foo %~ bar & baz .~ quux
  where
    bar :: Int -> Int
    bar = (+1)

    quux :: Int
    quux = 20

quux2 :: IO Int64
quux2 = (*) 1_000_000 . systemSeconds <$> getSystemTime
