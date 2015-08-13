{-# LANGUAGE DeriveFunctor #-}

module Tikhon where

data Context a = Context [a] a [a] deriving Functor

instance Applicative Context where
    pure x = Context [] x []
    Context fins fa fouts <*> Context xins xa xouts =
        Context (map ($ xa) fins ++ map fa xins)
                (fa xa)
                (map ($ xa) fouts ++ map fa xouts)

contextJoin :: Context (Context a) -> Context a
contextJoin (Context ins (Context innerIns node innerOuts) outs) =
    Context (concatMap (\(Context i x o) -> i ++ x : o) ins
             ++ innerIns)
            node
            (innerOuts ++
             concatMap (\(Context i x o) -> i ++ x : o) outs)

instance Monad Context where
    return x = Context [] x []
    m >>= f = contextJoin $ fmap f m
