{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module EitherT where

import Control.Monad.Catch
import Prelude hiding (catch)

newtype EitherT e m a = EitherT { runEitherT :: m (Either e a) }

instance MonadCatch m => MonadCatch (EitherT e m) where
    throwM = return . Left
    catch (EitherT m) c = EitherT $ \r -> m r `catch` \e -> runEitherT (c e) r
