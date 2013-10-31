{-# LANGUAGE TypeOperators #-}

module HOApplicative where

import Control.Monad.Free

data (f :-> g) a = NTrans (forall x. f x -> g x) a

headMay :: [a] -> Maybe a
headMay []    = Nothing
headMay (x:_) = Just x

(<<*>>) :: (Functor f, Functor g)
        => Free (f :-> g) a -> Free f a -> Free g a
Pure _ <<*>> _ = error "Uh oh"
Free _ <<*>> Pure _ = error "Uh oh"
Free (NTrans f xs) <<*>> ys = hoistFree f ys -- needs to be recursive on both arguments

{-

Example of use:

Free (NTrans headMay (Pure ("Hi" :: String))) <<*>> Free [Free [Pure ("Hi" :: String)]]

-}
