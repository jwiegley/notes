{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Printf where

import Data.Monoid
import Data.Text
import Data.Singletons.Prelude
import Data.Type.Equality
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

data Path :: * -> [*] -> * where
    Head :: Path x (x ': xs)
    Tail :: Path x xs -> Path x (x' ': xs)

data Format :: [*] -> [*] -> * where
    End  :: Format fs xs
    Str  :: Text -> Format fs xs -> Format fs xs
    Hole :: Show x => Path x xs -> Format fs xs -> Format (f ': fs) xs

getElement :: Path x xs -> List xs -> x
getElement _ Nil                 = error "Empty list in getElement"
getElement Head (Cons y _)       = y
getElement (Tail xs) (Cons _ ys) = getElement xs ys

printf :: Format fs xs -> List xs -> Text
printf End _             = ""
printf (Str t fmt) args  = t <> printf fmt args
printf (Hole p fmt) args = pack (show (getElement p args)) <> printf fmt args

head :: ((n :> 1) ~ True) => Vector n (x ': xs) -> x
head (VCons x _) = x

main :: IO ()
main = do
    print $ Printf.head (VCons 10 (VCons "Hello" VNil))
    print $ Printf.head (VCons "Hello" VNil)
    print $ Printf.head VNil
    print $ printf (Str "Hello "
            (Hole (Head :: Path String '[String, Int])
             (Hole (Tail (Head :: Path Int '[Int]) :: Path Int '[String, Int])
              (Str "!" End))))
        (Cons "John" (Cons 42 Nil))

data Vector :: Nat -> [*] -> * where
    VNil  :: Vector 0 '[]
    VCons :: x -> Vector n xs -> Vector (n + 1) (x ': xs)
