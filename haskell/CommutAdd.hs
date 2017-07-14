{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module CommutAdd where

import Data.Type.Equality
import GHC.TypeLits

commutative :: forall (a :: Nat) (b :: Nat). (a + b) :~: (b + a)
commutative = Refl
