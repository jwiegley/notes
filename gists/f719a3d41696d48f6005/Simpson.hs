{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}

module Nodes where

import Control.Lens
import Data.Data
import Data.Data.Lens

data NodeF (p :: * -> *) a = Null
            | CharNode Char
            | DoubleNode Double
            | IntNode Integer
            | StrNode String
            | Tuple [a]
            | Assign String a
            | BindingNode String
            | Call a a a
            | Def (p a) a a
            | Escape (p a) a (p a) a
            | Finally a a
            | Hide a
            | If a a a
            | Matcher (p a) a
            | Method a a [p a] a a
            | Noun String
            | Object a (p a) a a
            | Script a [a] [a]
            | Sequence [a]
            | Try a (p a) a
    deriving (Data, Eq, Functor, Show, Typeable)

instance (Data a, Typeable a, Typeable p, Data (p a)) => Plated (NodeF p a) where
    plate = uniplate

data PatternF (p :: * -> *) (a :: *) = Ignore (p a)
               | BindPattern String
               | Final String (p a)
               | ListPattern [a]
               | Var String (p a)
               | Via (p a) a
    deriving (Data, Eq, Functor, Show, Typeable)

instance (Data a, Typeable a, Typeable p, Data (p a)) => Plated (PatternF p a) where
    plate = uniplate

newtype Fix f = Fix { outF :: f (Fix f) }

type Pattern = Fix (PatternF (NodeF Pattern))

type Node = Fix (NodeF Pattern)
