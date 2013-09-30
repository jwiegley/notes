{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Control.Applicative
import Control.Comonad
import Data.List.NonEmpty as NE
import Control.Comonad.Store
import Data.Map as M

{-
class Functor w => Comonad w where
  extract :: w a -> a
  extend :: (w a -> b) -> w a -> w b

instance Comonad ((,) e) where
  extract = snd
  extend f t@(e,_) = (e, f t)
-}

printString :: a -> (a -> b) -> b
printString x f = f x

data Foo a b = Foo { fooName  :: a
                   , fooValue :: b }

instance Functor (Foo a) where
  fmap f (Foo { fooName = e, fooValue = t }) =
    Foo { fooName = e, fooValue = f t }

instance Comonad (Foo a) where
  extract = fooValue
  extend f x@(Foo { fooName = e, fooValue = _ }) =
    Foo { fooName = e, fooValue = f x }

data Bar a b = Bar { barName  :: a
                   , barValue :: b }

instance Functor (Bar a) where
  fmap f (Bar { barName = e, barValue = t }) =
    Bar { barName = e, barValue = f t }

instance Comonad (Bar a) where
  extract = barValue
  extend f x@(Bar { barName = e, barValue = _ }) =
    Bar { barName = e, barValue = f x }

codeNeedingValue :: (Comonad a) => a b -> b
codeNeedingValue = extract

ask :: (e, a) -> e
ask = fst

local :: (e -> e) -> (e,a) -> (e,a)
local f (e,a) = (f e,a)

type Named a b = (a,b)
type NamedInt = Named String Int

foo :: NamedInt -> IO ()
foo nint = do
  print $ ask nint
  print $ extract nint
  print $ fmap (1+) nint
  print $ local ("Name: "++) nint

------------------------------------------------------------------------------

{-
data Store s a = Store (s -> a) s

instance Functor (Store s) where
  fmap f (Store g s) = Store (f . g) s

instance Comonad (Store s) where
  extract (Store f s) = f s
  extend f (Store g s) = Store (\s' -> f (Store g s')) s
-}

type MapStore k v = Store k (Maybe v)

foo' :: MapStore Int Int -> IO ()
foo' st = do
  print $ extract st
  print $ peek 2 st
  let st' = seeks (+1) st       -- st' is now "based" at 4
  print $ (+) <$> peeks pred st' <*> peeks succ st'

bar' :: IO()
bar' =
  foo' $ store (\k -> M.lookup k $ M.fromList [ (1, 100)
                                              , (2, 200)
                                              , (3, 300)
                                              , (4, 400)
                                              , (5, 500) ])
               3

-- type MapStore k v = Store (Map k) v

newtype MyNonEmpty a = MyNonEmpty { getMyNonEmpty :: NonEmpty a }
    deriving (Functor, Applicative, Monad, Show)

neLength :: NonEmpty a -> Int
neLength (_ :| xs) = 1 + length xs

instance Comonad MyNonEmpty where
    extract (MyNonEmpty (a :| _)) = a
    extend f (MyNonEmpty w) = MyNonEmpty $ NE.map f (NE.map (MyNonEmpty . NE.fromList) (NE.fromList (NE.take (neLength w) (NE.tails w))))

main :: IO ()
main = undefined
