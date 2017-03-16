{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Tikhon2 where

infixr :+

data a :+ b = Inl a | Inr b
    deriving Show

class Variant a b where
    construct :: a -> b

instance Variant a a where
    construct = id

instance {-# OVERLAPPING #-} Variant a (a :+ b) where
    construct = Inl

instance Variant a c => Variant a (b :+ c) where
    construct = Inr . construct

class Destructor a b where
    destruct :: a -> Maybe b

instance Destructor a a where
    destruct = Just

instance Destructor a b where
    destruct = const Nothing

instance {-# OVERLAPPING #-} Destructor (a :+ b) a where
    destruct (Inl a) = Just a
    destruct _ = Nothing

instance {-# OVERLAPPING #-} Destructor b c => Destructor (a :+ b) c where
    destruct (Inl a) = destruct a
    destruct (Inr a) = destruct a

foo :: Int :+ Char :+ Double
foo = construct 'a'

bar :: Int :+ Char :+ Double -> Maybe Char
bar = destruct
