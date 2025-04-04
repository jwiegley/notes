{-# LANGUAGE TypeFamilies, ConstraintKinds, TypeSynonymInstances,
             FlexibleInstances, RankNTypes, UndecidableInstances,
             OverloadedStrings, IncoherentInstances #-}

class Foo a where
  foo :: a -> Int

instance {-# OVERLAPPING #-} Foo String where
  foo _ = 100

instance Real a => Foo a where
  foo = floor . toRational

main :: IO ()
main = do
  print $ foo ("Hello" :: String)
  print $ foo (10 :: Int)
  print $ foo (10 :: Float)
  print $ foo (10 :: Integer)
