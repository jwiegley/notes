{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Printf where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Proxy
import Data.Text
import Data.Type.Equality
import Data.Void
import GHC.TypeLits

{-
Every function of multiple arguments is isomorphic to its "uncurried" form of
a function in one argument taking an N-tuple.

A "varargs function" is then equivalent to a function taking an N-tuple whose
size is determined at runtime.  To model this, we use a type level list, which
means we only need a way to construct such a list.
-}

data List :: [*] -> * where
    Nil  :: List '[]
    Cons :: Show x => x -> List xs -> List (x ': xs)

data Path :: * -> [*] -> * where
    Head :: Path x (x ': xs)
    Tail :: Path x xs -> Path x (x' ': xs)

data Format :: [*] -> * where
    End  :: Format xs
    Str  :: Text -> Format xs -> Format xs
    Hole :: Show x => Path x xs -> Format xs -> Format (x ': xs)

getElement :: Path x xs -> List xs -> x
getElement Head (Cons y _)       = y
getElement (Tail xs) (Cons _ ys) = getElement xs ys

printf :: Format xs -> List ys -> Text
printf (Str t fmt) args = t <> printf fmt args
printf (Hole p fmt) args =
    pack (show (getElement p args)) <> printf fmt args

main :: IO ()
main = print $
    printf (Str "Hello "
            (Hole (Head :: Path String '[String, Int])
             (Hole (Tail (Head :: Path Int '[Int]) :: Path Int '[String, Int])
              (Str "!" End))))
        (Cons "John" (Cons 42 Nil))
