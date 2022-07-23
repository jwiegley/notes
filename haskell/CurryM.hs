module CurryM where

import Control.Monad.Trans.RWS

uncurryM ::
  Monoid w =>
  (a -> RWST r w s (Either e) (b -> RWST r w s (Either e) c)) ->
  ((a, b) -> RWST r w s (Either e) c)
uncurryM f (a, b) = do
  f' <- f a
  f' b

curryM ::
  Monoid w =>
  ((a, b) -> RWST r w s (Either e) c) ->
  (a -> RWST r w s (Either e) (b -> RWST r w s (Either e) c))
curryM f = pure . curry f
