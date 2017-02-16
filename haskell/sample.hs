import Control.Monad

foo :: (Num a) => Maybe a -> Maybe a
foo arg = do
  x <- arg
  case Just 11 of
    Just z  -> return $ x + z
    Nothing -> Nothing

{-
  do a <- b
     ...

  is the same as writing:
  
  b >>= (\a -> ...)
-}

foo' :: (Num a) => Maybe a -> Maybe a
foo' arg =
  arg >>= (\x -> case Just 11 of
                   Just z  -> return $ x + z
                   Nothing -> Nothing)

{-
  (=~) :: String -> String -> Bool
  str =~ pat = ...

  (=~) :: String -> String -> String
  str =~ pat = ...
-}

<$> :: (a -> b) -> f a -> f b
>>= :: m a -> (a -> m b) -> m b
>>> :: m a b -> (a -> m b) -> m b

Maybe String

fmap length (Just "")          => 0

instance Functor Maybe where
  fmap :: (a -> b) -> f a -> f b

instance Functor (Either a) where
  fmap :: (a -> b) -> f a -> f b

data Both a b = Both { fromLeft :: a, fromRight :: b }

instance Category Both where
  (>>>) :: Both a b -> Both b c -> Both a c
  x (>>>) y :: Both (fromLeft x) (fromRight y)


getStr :: IO String
getStr :: IO Int

Both a b -> Both b c

a ...-> (f >>> g >>> h) ...-> c
a ...-> (f .   g .   h) ...-> c


foo :: Category a b -> Category a c
foo f g = (x >>> y) f g
liftM length' =<< (Just "")    => Nothing

length $   "foo"
length <$> (Just "foo")

(\x y z -> x ++ y ++ z) <$> (Just "foo") <*> (Just "bar") <*> (Just "baz")

