{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}

module Ertes where

data Stream f m r = Step  (f (Stream f m r))
                  | Delay (m (Stream f m r))
                  | Return r

data Step s a r = Done r | Skip s | Yield s a deriving Functor

data Stream' a m r = forall s. Stream' (s -> m (Step s a r)) s
