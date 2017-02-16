{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Teletype where

import           Control.Exception
import           Control.Monad.Error.Class
import           Data.Functor.Identity
import           Data.Functor.Sum
import           Streaming
import           Streaming.Internal
import qualified Streaming.Prelude as S

-- By parameterizing over 't', we keep the choice of input effects out of the
-- grammar; we are not even required to relate 't' to 'r'.
data TeletypeF a b t r = Get (a -> r)
                       | GetMany (t (Sum ((->) a) (TeletypeF a b t)) r)
                       | Put b r

deriving instance Functor (t (Sum ((->) a) (TeletypeF a b t)))
    => Functor (TeletypeF a b t)

newtype StreamM m a r = StreamM { getStreamM :: Stream a m r }
    deriving (Functor, Applicative, Monad)

-- This "await grammar" is based on the 'streaming' library, but we could swap
-- it out for 'FreeT' or pipes without changing TeletypeF.
await :: (Monad m, Functor f) => StreamM m (Sum ((->) a) f) a
await = StreamM (Step (InL return))

teletype :: (Monad m, Functor f) => Stream f m b -> StreamM m (Sum ((->) a) f) b
teletype = StreamM . S.maps InR

type Teletype  a b   = Stream (TeletypeF a b (StreamM Identity)) Identity
type TeletypeT a b m = Stream (TeletypeF a b (StreamM m)) m

-- These smart constructors work for either Free or FreeT constructions.
get :: Monad m => TeletypeT a b m a
get = Step (Get return)

put :: Monad m => b -> TeletypeT a b m ()
put x = Step (Put x (return ()))

getMany :: Monad m
        => StreamM m (Sum ((->) a) (TeletypeF a b (StreamM m))) c
        -> TeletypeT a b m c
getMany m = Step (GetMany (Return <$> m))

-- The pure evaluator (over Identity, taking input as a list of strings, and
-- giving output as the same).
phi :: TeletypeF String String (StreamM Identity) (Identity ([String] -> (r, [String])))
    -> Identity ([String] -> (r, [String]))
phi (Get k)   = Identity $ \(x:xs) -> runIdentity (k x) xs
phi (Put s r) = Identity $ \xs -> let (r', os) = runIdentity r xs in (r', s:os)
phi (GetMany (StreamM term)) = iterT psi (runIdentity <$> term)
  where
    -- InR is the TeletypeF functor
    psi (InR x) = Identity $ runIdentity (phi x)
    -- InL is the (->) a functor, which represents an inner Get
    psi (InL k) = Identity $ \(x:xs) -> runIdentity (k x) xs

-- The impure evaluator (over some 'm' based in IO, using getLine and putStrLn
-- for the effects).
phiM :: (MonadError IOException m, MonadIO m)
     => TeletypeF String String (StreamM m) (m r) -> m r
phiM (Get k)   = liftIO getLine >>= k
phiM (Put s r) = liftIO (putStrLn s) >> r
phiM (GetMany (StreamM term)) = join $ iterT psiM term
  where
    psiM (InR x) = phiM x
    psiM (InL k) = do
        s <- liftIO getLine
        if s == "error"
            then throwError (userError "User signalled an error")
            else do
                -- Without this, only 2 reads are done instead of 3 in ghci
                liftIO $ putStrLn $ "read: " ++ s
                k s

-- This term now works for both the pure and the impure cases
foo :: Monad m => TeletypeT String String m ()
foo = do
  a <- get
  put a
  getMany $ do
      x <- await
      teletype $ put x
      y <- await
      teletype $ put y
      z <- await
      teletype $ put z
  return ()

main :: IO ()
main = do
    print $ runIdentity (iterT phi (const ((), []) <$ foo))
        ["1", "2", "3", "4"]
    iterT phiM foo
