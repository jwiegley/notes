{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Transformer where

import Control.Monad.Trans.Either

class MonadHoist (t :: (* -> *) -> * -> *) m | t -> m where
    promote :: m a -> t m a

instance MonadHoist (EitherT e) (Either e) where
    promote = EitherT . return
