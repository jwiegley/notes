{-# LANGUAGE TypeFamilies #-}

import Data.Constraint
import Data.Set
import Test.QuickCheck

class RFunctor f where
    type C f :: * -> Constraint
    rfmap :: (C f a, C f b) => (a -> b) -> f a -> f b

instance RFunctor Set where
    type C Set = Ord
    rfmap = Data.Set.map

data AlwaysEqual a = Wrap { unWrap :: a }
instance Eq (AlwaysEqual a) where
    _ == _ = True
instance Ord (AlwaysEqual a) where
    compare _ _ = EQ

instance (Ord a, Arbitrary a) => Arbitrary (Set a) where
    arbitrary = fromList <$> arbitrary

prop_rfmap_law_2 :: Set Int -> Bool
prop_rfmap_law_2 x =
    rfmap unWrap (rfmap Wrap x) == rfmap (unWrap . Wrap) (x :: Set Int)

main :: IO ()
main = quickCheck prop_rfmap_law_2
