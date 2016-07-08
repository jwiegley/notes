{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module FunType where

type family Fun (dom :: [*]) (cod :: *) where
    Fun '[] ys = ys
    Fun (x ': xs) ys = x -> Fun xs ys

foo :: Fun [Int, Double] Char
foo x y = 'a'
