{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Main where

import           Control.Applicative
import           Control.Monad.Free
import           Data.Functor.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as Set

data Lookup k v a = Lookup (Set k) (Map k v -> a)

instance Functor (Lookup k v) where
    fmap f (Lookup k h) = Lookup k (f . h)

newtype Query k v a = Query (Free (Lookup k v) a) deriving Functor

instance Ord k => Applicative (Query k v) where
    pure x = Query (Pure x)
    Query (Pure f) <*> Query (Pure x) = Query (Pure (f x))
    Query (Free (Lookup fk f)) <*> Query (Pure x) =
        Query (Free (Lookup fk (fmap ($ x) . f)))
    Query (Pure f) <*> Query (Free (Lookup xk x)) =
        Query (Free (Lookup xk (fmap f . x)))
    Query (Free (Lookup fk f)) <*> Query (Free (Lookup xk x)) =
        Query (Free (Lookup (fk <> xk)
                     (\m -> fmap ($ iter (\(Lookup _ f') -> f' m) (x m)) (f m))))

class KeyValueStore (s :: * -> * -> *) (m :: * -> *) where
    runQuery :: Ord k => Query k v a -> s k v -> m a

instance KeyValueStore Map Identity where
    runQuery (Query x) m = return $ iter (\(Lookup _ f) -> f m) x

(@?) :: Ord k => (v -> a) -> k -> Query k v a
f @? k = Query (Free (Lookup (Set.singleton k) (Pure . f . (Map.! k))))

main :: IO ()
main = do
    print $ runIdentity $ runQuery
        (pure 10 :: Query Int String Int)
        (Map.fromList [(10, "Hello")])

    print $ runIdentity $ runQuery
        ((++) <$> id @? 10 <*> id @? 20 :: Query Int String String)
        (Map.fromList [(10, "Hello"), (20, "Goodbye")])
