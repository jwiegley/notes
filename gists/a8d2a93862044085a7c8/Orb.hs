{-# LANGUAGE GADTs #-}

data Wrap a where
    Atom :: Show a => a -> Wrap a
    FMap :: Show a => (a -> b) -> Wrap a -> Wrap b

-- This doesn't work:
myShow :: Show a => Wrap a -> String
myShow (Atom a) = show a
myShow (FMap f a) = myShow a
