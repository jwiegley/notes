{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module FreeInvol where

import Control.Monad.Free
import Test.QuickCheck

instance Arbitrary (Free [] Int) where
    arbitrary = frequency
        [ (2, Pure <$> arbitrary)
        , (1, Free <$> arbitrary) ]

instance Arbitrary (Free [] (Free [] Int)) where
    arbitrary = frequency
        [ (1, Pure <$> arbitrary)
        , (1, Free <$> arbitrary) ]

prop_Free_sequence_involutive :: Free [] (Free [] Int) -> Bool
prop_Free_sequence_involutive x = sequenceA (sequenceA x) == x

main = quickCheck prop_Free_sequence_involutive
