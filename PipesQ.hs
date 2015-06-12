{-# LANGUAGE OverloadedStrings #-}

module PipesQ where

import Control.Applicative
import Pipes as P
import Pipes.Prelude as P
import Pipes.Group as P
import Control.Lens
import Data.Function
import Data.Monoid

-- foldValues :: (Monad m, Eq k)
--            => (v -> v -> v) -> Producer (k, v) m r -> Producer (k, v) m r
-- foldValues append xs =
--     P.concat <-< folds step Nothing id (view (groupsBy ((==) `on` fst)) xs)
--   where
--     step Nothing        (k, v) = Just (k, v)
--     step (Just (_, v0)) (k, v) = Just (k, v0 `append` v)

foldValues :: (Monad m, Eq k) => (v -> v -> v) -> Pipe (k, v) (k, v) m r
foldValues append = loop Nothing
  where
    loop mx = do
        (k, v) <- await
        yield (k, maybe v (`append` v) mx)
        loop (Just v)
