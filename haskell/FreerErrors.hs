{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module FreerErrors where

import Control.Applicative
import Control.Exception hiding (catch)
import Control.Monad.Catch
import Control.Monad.Freer
import Control.Monad.Reader
import Data.Functor.Identity
import Data.OpenUnion.Internal
import Data.Typeable

type MonoLens a b = forall f. Functor f => (b -> f b) -> a -> f a

over :: MonoLens a b -> (b -> b) -> a -> a
over l f = runIdentity . l (Identity . f)

view :: MonoLens a b -> a -> b
view l = getConst . l Const

class Has a b where
    hasLens :: MonoLens a b

data Level = Fatal | Error | Warning | Info | Debug
    deriving (Ord, Eq, Bounded, Enum, Show)

data Frame s = forall t. Frame Level (Union s t)

type Frames s = [Frame s]

type Framed e m s =
    (MonadReader e m, Has e (Frames s), Typeable s, MonadThrow m)

instance Has (Frames s) (Frames s) where
    hasLens f = f

newtype MyException s = MyException (Frames s)

instance Show (MyException s) where
    show _ = "Exception"

instance Typeable s => Exception (MyException s)

withFrame :: forall s e m a. Framed e m s => Level -> Eff s String -> m a -> m a
withFrame level frame = local (over hasLens (Frame level frame :))

throwError :: forall s e m a. (Framed e m s, MonadThrow m) => Eff s String -> m a
throwError frame = do
    context <- asks (view hasLens)
    throwM $ MyException (Frame Error frame:context)

data MyInfo a where
    SomeInfo :: MyInfo String
    ErrorOne :: MyInfo String
    ErrorTwo :: MyInfo String

-- | For a web browser, we might want to render errors much differently,
--   allowing the user to drill down into associated bits of info. The default
--   requires that it least be enough information to be equvialent to Show,
--   though other effect handlers might just always return "" from some State
--   monad that collects the information in a different form.
renderMyInfo :: Eff (MyInfo ': r) a
             -> Eff r a
renderMyInfo = interpret $ \case
    SomeInfo -> pure "Just some info, never mind:"
    ErrorOne -> pure "Error one"
    ErrorTwo -> pure "Error two"

-- | 'foo' only needs to care about its own kinds info frames or errors, even
--   if it ends up being used in a context where a lot more information is
--   available.
foo :: forall s e m. (Framed e m s, Member MyInfo s) => Int -> m Int
foo n = withFrame @s Debug (send SomeInfo) $ do
    throwError @s (send ErrorOne)  -- oops!
    return $ n + 20

main :: IO ()
main = do
    x <- flip runReaderT [] $
        catch (foo @'[MyInfo] @(Frames '[MyInfo]) 100) $ \case
            MyException frames -> do
                forM_ (reverse frames) $ \(Frame _level frame) ->
                    liftIO $ putStrLn $ run $ renderMyInfo frame
                return 0
    print x
