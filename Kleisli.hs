{-# LANGUAGE FlexibleInstances #-}

module Kleisli where

import Control.Arrow
import Control.Monad

instance Monad m => Monoid (Kleisli m a a) where
    mempty = Kleisli return
    x `mappend` y = Kleisli $ runKleisli x >=> runKleisli y
