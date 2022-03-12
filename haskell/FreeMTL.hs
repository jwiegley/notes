{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module FreeMTL where

import Control.Monad.Free

class MyAlgebraMTL m where
  speakLoudly :: m ()

data MyAlgebraF r
  = SpeakLoudly r
  deriving Functor

type MyAlgebraFree = Free MyAlgebraF

instance MyAlgebraMTL MyAlgebraFree where
    speakLoudly = Free (SpeakLoudly (Pure ()))
