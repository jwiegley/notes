{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

module IsoMu where

import Data.Functor.Compose

data Of a b = Of a b deriving (Show, Functor)

newtype Mu f = Mu { runMu :: forall r. (f r -> r) -> r}

muMaybe :: Mu Maybe
muMaybe = Mu $ \k -> k Nothing -- muMaybe = Mu $ \k -> k (Just <anything>)

muToList :: Mu (Compose Maybe (Of a)) -> [a]
muToList (Mu k) = k $ \(Compose x) -> case x of
    Nothing -> []
    Just (Of h t) -> h:t

muFromList :: [a] -> Mu (Compose Maybe (Of a))
muFromList xs    = Mu $ \k -> k $ Compose $ case xs of
    []    -> Nothing
    (h:t) -> Just (Of h (runMu (muFromList t) k))

muToStream :: Mu (Of a) -> [a]
muToStream (Mu k) = k $ \(Of h t) -> h : t

data Nu f = forall x. Nu x (x -> f x)

nuMaybe :: Nu Maybe
nuMaybe = Nu () (const Nothing) -- nuMaybe = Nu <anything> Just

nuToList :: Nu (Compose Maybe (Of a)) -> [a]
nuToList (Nu x fx) = go (fx x)
  where
    go (Compose Nothing) = []
    go (Compose (Just (Of h t))) = h : go (fx t)

nuFromList :: [a] -> Nu (Compose Maybe (Of a))
nuFromList xs = Nu xs $ \z -> case z of
    []     -> Compose Nothing
    (y:ys) -> Compose (Just (Of y ys))

nuToStream :: Nu (Of a) -> [a]
nuToStream (Nu x fx) = go (fx x)
  where
    go (Of h t) = h : go (fx t)

muToNu :: Functor f => Mu f -> Nu f
muToNu (Mu k) = let f _ = k $ \fr -> k (fmap f fr) in Nu _ f

nuToMu :: Functor f => Nu f -> Mu f
nuToMu (Nu x fx) = Mu $ \k -> let f = k . fmap f . fx in f x

main :: IO ()
main = do
    print (muToList (muFromList ([1..10] :: [Int])))
    print (nuToList (nuFromList ([1..10] :: [Int])))
    print (nuToList (muToNu (muFromList ([1..10] :: [Int]))))
    print (muToList (nuToMu (nuFromList ([1..10] :: [Int]))))
