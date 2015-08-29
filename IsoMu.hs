{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}

module IsoMu where

import Data.Functor.Compose

data Of a b = Of a b deriving Functor

newtype Mu f = Mu { runMu :: forall r. (f r -> r) -> r}

muToStream :: Mu (Of a) -> [a]
muToStream (Mu k) = k $ \(Of h t) -> h : t

muToList :: Mu (Compose Maybe (Of a)) -> [a]
muToList (Mu k) = k $ \(Compose x) -> case x of
    Nothing -> []
    Just (Of h t) -> h:t

muFromList :: [a] -> Mu (Compose Maybe (Of a))
muFromList xs    = Mu $ \k -> k $ Compose $ case xs of
    []    -> Nothing
    (h:t) -> Just (Of h (runMu (muFromList t) k))

data Nu f = forall x. Nu x (x -> f x)

nuToStream :: Nu (Of a) -> [a]
nuToStream (Nu x fx) = go (fx x)
  where go (Of h t) = h : go (fx t)

nuToList :: Nu (Compose Maybe (Of a)) -> [a]
nuToList (Nu x fx) = go (fx x)
  where go (Compose Nothing) = []
        go (Compose (Just (Of h t))) = h : go (fx t)

nuFromList :: [a] -> Nu (Compose Maybe (Of a))
nuFromList xs = Nu xs $ \z -> case z of
    []     -> Compose Nothing
    (y:ys) -> Compose (Just (Of y ys))

muToNu :: Functor f => Mu f -> Nu f
muToNu (Mu k) = k $ \fnu -> Nu fnu (fmap (\(Nu x fx) -> fmap (`Nu` fx) (fx x)))

nuToMu :: Functor f => Nu f -> Mu f
nuToMu (Nu x fx) = Mu $ \k -> let f = k . fmap f . fx in f x

newtype Fix f = Fix { unFix :: f (Fix f) }

fixToStream :: Fix (Of a) -> [a]
fixToStream (Fix (Of h t)) = h : fixToStream t

fixToList :: Fix (Compose Maybe (Of a)) -> [a]
fixToList (Fix (Compose Nothing)) = []
fixToList (Fix (Compose (Just (Of h t)))) = h : fixToList t

fixFromList :: [a] -> Fix (Compose Maybe (Of a))
fixFromList xs = Fix $ case xs of
    []     -> Compose Nothing
    (y:ys) -> Compose (Just (Of y (fixFromList ys)))

muToFix :: Mu f -> Fix f
muToFix (Mu k) = k Fix

fixToMu :: Functor f => Fix f -> Mu f
fixToMu (Fix x) = Mu $ \k -> let f = k . fmap (f . unFix) in f x

nuToFix :: Functor f => Nu f -> Fix f
nuToFix (Nu x fx) = Fix $ fmap (nuToFix . (`Nu` fx)) (fx x)

fixToNu :: Fix f -> Nu f
fixToNu x = Nu x unFix

main :: IO ()
main = do
    let xs = [1..10] :: [Int]

    print $ xs == muToList  (muFromList xs)
    print $ xs == nuToList  (nuFromList xs)

    print $ xs == nuToList  (muToNu  (muFromList xs))
    print $ xs == muToList  (nuToMu  (nuFromList xs))

    print $ xs == muToList  (fixToMu (fixFromList xs))
    print $ xs == fixToList (muToFix (muFromList xs))

    print $ xs == nuToList  (fixToNu (fixFromList xs))
    print $ xs == fixToList (nuToFix (nuFromList xs))
