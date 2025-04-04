{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Gyph where

import GHC.TypeLits

data Person :: [Symbol] -> * where
    Person :: KnownSymbol n
           => proxy n -> Person ancestors -> Person (n ': ancestors)
