module FixAndFree where

Fix f = Free f Void
Free f a = Fix (Either a . f) ()

newtype Fix f = Fix (f (Fix f))

data Free f a
  = Pure a
  | Free (f (Pure f a))
