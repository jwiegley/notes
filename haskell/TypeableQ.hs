{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module TypeableQ where

import Control.Exception
import Data.Typeable

newtype Foo m = Foo (m Int) deriving Typeable

instance Show (Foo m) where show (Foo _) = "Foo"

instance Typeable m => Exception (Foo m)

render :: forall m. Typeable m => SomeException -> m Int
render f | Just (Foo e :: Foo m) <- fromException f = e
         | otherwise = error "failed!"

main :: IO ()
main = do
    x <- catch (100 <$ throw (Foo @IO (pure 10))) render
    print x
