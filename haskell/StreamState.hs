{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}

module StreamState where

import Data.Function

newtype Stream a = Stream (Int -> a)

newtype Transformer a b = Transformer (Stream a -> Stream b)

data Mealy a b = forall s. Mealy
  { current :: s,
    step :: a -> s -> (s, b)
  }

mealyDenote :: Mealy a b -> Transformer a b
mealyDenote Mealy {..} = Transformer $ \(Stream input) ->
  let output = fix $ \k n ->
          step (input n)
               (case n of
                  0  -> current
                  n' -> fst (k (pred n')))
  in Stream (snd . output)
