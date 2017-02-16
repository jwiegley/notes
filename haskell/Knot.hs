module Knot where

import Data.Functor.Identity

newtype Fix f a = Fix { getFix :: f (Fix f a) }

type Infinite a = Fix Identity a

main = do
    let x = Fix (Identity x)
    print "hmm"
