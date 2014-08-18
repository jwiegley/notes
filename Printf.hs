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
    Cons :: x -> List xs -> List (x ': xs)

class GetElement xs where
    type Result xs :: *
    getElement :: Int -> List xs -> Result xs

instance GetElement '[] where
    type Result '[] = Void

instance GetElement xs => GetElement (x ': xs) where
    type Result (x ': xs) = x
    getElement 0 (Cons x _)  = x
    getElement n (Cons _ xs) = getElement (n - 1) xs

data Format :: [*] -> * where
    End  :: Format '[]
    Str  :: Text -> Format xs -> Format xs
    Hole :: Int -> Proxy x -> Format xs -> Format (x ': xs)

printf :: (Show x, GetElement xs) => Format (x ': xs) -> List (x ': xs) -> Text
printf (Str t fmt) args = t <> printf fmt args
printf (Hole i _ fmt) args =
    pack (show (getElement i args)) <> printf (castWith proof fmt) args
  where
    proof :: Format xs :~: Format (x ': xs0)
    proof = undefined

main :: IO ()
main = print $
    printf (Str "Hello "
            (Hole 0 (Proxy :: Proxy String)
             (Hole 1 (Proxy :: Proxy Int)
              (Str "!"
               End))))
        (Cons "John" (Cons 42 Nil))
