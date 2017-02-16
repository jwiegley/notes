{-# LANGUAGE DeriveFunctor #-}

module Data.Evolutionary.EV where

import Prelude hiding (empty)

import Control.Monad.Free

data EVR s r a = Step s r |
                 Start s a
                 deriving (Functor)

type EV s r = Free (EVR s r)

-- wanna now write a function for starting, based on what you pasted:

start x y = Free (Start x y)

-- Complaint:
--
-- • Non type-variable argument
--    in the constraint: MonadFree (EVR s r) m 
--  (Use FlexibleContexts to permit this)
-- • When checking the inferred type
--    start :: forall (m :: * -> *) a s r.
--             MonadFree (EVR s r) m =>
--             s -> a -> m a
