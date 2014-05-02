module Foo where

import Data.Functor

newtype Fix f = Fix { unFix :: f (Fix f) }

type Name = String

data ASTF f a = ASTF Name [f a]

type AST a = Fix (ASTF a)

data ASTPat a = AST (ASTPat a) | ASTVar a
