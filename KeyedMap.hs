{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

module KeyedMap where

import Data.Map

data KeyedMap :: * -> [*] -> * where
    Here :: x -> KeyedMap a xs -> KeyedMap a (x ': xs)
    There :: x -> KeyedMap a xs -> KeyedMap a (x ': xs)
