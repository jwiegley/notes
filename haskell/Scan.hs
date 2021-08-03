{-# LANGUAGE ScopedTypeVariables #-}

module Scan where

type Nat = Int -- quiet, Conal! :-)

type Stream a = Nat -> a

listToStream :: [a] -> Stream a
listToStream [] = error "Cannot make finite list into stream"
listToStream (x : xs) = \n ->
  if n == 0 then x else listToStream xs (n - 1)

streamToList :: Stream a -> [a]
streamToList f = go 0
  where
    go n = f n : go (n + 1)

-- A casaul stream transform has the restriction that any answer at position N
-- may only consult positions 1-(N-1) from the input.
type StreamTransform a b = Stream a -> Stream b

-- scanr :: (a -> b -> b) -> b -> [a] -> [b]

-- This is unnecessary beacuse 'f' can simply close over the environment
reader env f z = map snd . scanr (\a (env', b) -> (env', f b a)) (env, z)

state f s = scanr f s

-- A specialization of state where you keep every state that is 'put' and you
-- never 'get'.
writer f s = scanr f s

-- Cont is a bastardization used to provide a meaning to 'goto'.

maybe f z = scanr (\(t, b) a -> if t then (True, f b a) else (False, b)) (True, z)

-- Q: Can I write all the various Pipes into the pipes library as scans.

-- Producer   = Pipe Void a ()
-- Pipe       = Pipe a b ()
-- Consumer r = Pipe a Void r

-- Producer a   = [a]
-- Pipe a b     = [a] -> [b]
-- Consumer a r = [a] -> r

-- Pipe a b m r = [a] -> [b]

-- scanM :: Monad m => (a -> b -> m a) -> a -> [b] -> m [a]

data Fold a b = Fold
  { step :: a -> b -> b,
    start :: b
  }

compose :: forall a b c. Fold a b -> Fold b c -> Fold a (b, c)
compose (Fold s1 z1) (Fold s2 z2) =
  Fold
    { step = \a (b, c) ->
        let intermediate = s1 a b
            result :: c = s2 intermediate c
         in (intermediate, result),
      start = (z1, z2)
    }

scan :: Fold a b -> StreamTransform a b
scan (Fold f z) = listToStream . scanr f z . streamToList

fold :: Fold a b -> Stream a -> b
fold (Fold f z) = foldr f z . streamToList
