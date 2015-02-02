{-# language GeneralizedNewtypeDeriving #-}

module Main where

import Data.Monoid

newtype Diff a = Diff (Endo a) deriving Monoid

diff :: Monoid a => a -> Diff a
diff k = Diff (Endo (k <>))

getDiff :: Monoid a => Diff a -> a
getDiff (Diff (Endo k)) = k mempty

main :: IO ()
main = print $ getDiff $ diff ("Foo" :: String) <> diff "Bar" <> diff "Baz"
