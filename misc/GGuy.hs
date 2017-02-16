{-# LANGUAGE DeriveGeneric, FlexibleInstances, ExistentialQuantification, ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module GGuy where

import Data.Constraint

data H c = forall a. (c a) => H a

instance Show (H Show) where
  show (H a) = show a

class IsInt a where
  getInt :: a -> Int

instance IsInt (H IsInt) where
  getInt (H a) = getInt a

instance IsInt Int where
  getInt x = x

data Showable :: (* -> Constraint) -> * where
    Shown :: Showable Show
    Inted :: Showable IsInt

testData :: Showable c -> [H c]
testData Shown = [H (1 :: Int), H (2 :: Int)]
testData Inted = [H (1 :: Int), H (2 :: Int)]

main :: IO ()
main = do
  putStrLn $ show $ (testData Shown :: [H Show]) --testData becomes [H Show]
  putStrLn $ show $ foldr (\x y -> y + (getInt x)) 0 (testData Inted :: [H IsInt]) --because testData is now [H Show] this fails
