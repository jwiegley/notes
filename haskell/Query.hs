{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import           Control.Applicative
import           Control.Monad.Free
import           Control.Monad.Logger
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Resource
import           Data.Functor.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as Set
import           Database.Esqueleto
import           Database.Persist.TH
import           Database.Persist.Sqlite

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
        Query (Free (Lookup (fk <> xk) (\m -> f m <*> x m)))

runMapQuery :: Monad m => Query k v a -> Map k v -> m a
runMapQuery (Query x) m = return $ iter (\(Lookup _ f) -> f m) x

share [mkPersist sqlSettings, mkMigrate "migrateAll"]
    [persistLowerCase|
        Person
            name String
            age Int Maybe
    |]

runDbQuery (Query (Pure x)) _ = return x
runDbQuery (Query (Free (Lookup keys f))) kf = do
    liftIO $ putStrLn "Calling runDbQuery"
    xs <- select $ from $ \t -> do
        where_ $ t^.kf `in_` valList (Set.toList keys)
        return t
    let q = f $ Map.fromList $ map (\(Entity k v) -> (k,v)) xs
    runDbQuery (Query q) kf

(@?) :: (Show k, Ord k) => (v -> a) -> k -> Query k v a
f @? k = Query (Free (Lookup (Set.singleton k) (Pure . f . lookupOrElse k)))
  where
    lookupOrElse k' m = case Map.lookup k' m of
        Nothing -> error $ "Failed to lookup key " ++ show k'
        Just x  -> x

main :: IO ()
main = do
    print $ runIdentity $ runMapQuery
        (pure 10 :: Query Int String Int)
        (Map.fromList [(10, "Hello")])

    print $ runIdentity $ runMapQuery
        ((++) <$> id @? 10 <*> id @? 20 :: Query Int String String)
        (Map.fromList [(10, "Hello"), (20, "Goodbye")])

    withSqliteConn "foo.db" $ \conn ->
        runNoLoggingT $ runResourceT $ flip runSqlConn conn $ do
            runMigration migrateAll
            insert_ $ Person "One" (Just 1)
            insert_ $ Person "Two" (Just 2)
            insert_ $ Person "Three" (Just 3)
            insert_ $ Person "Four" (Just 4)
            insert_ $ Person "Five" (Just 5)
            let k x = Key $ PersistInt64 x
                q = (++) <$> personName @? k 2 <*> personName @? k 3
            liftIO . print =<< runDbQuery q PersonId
