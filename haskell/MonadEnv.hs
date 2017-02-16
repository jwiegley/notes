{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module MonadEnv where

import Control.Applicative
import Control.Lens
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader (ReaderT(..), runReaderT)
import Data.Proxy
import Data.Reflection
import Data.Text
import Language.Haskell.TH.Syntax (Lift (lift), Q, Exp, Loc (..), qLocation)
import System.Log.FastLogger

type MonadEnv env a m = (Monad m, MonadReader env m)

askE :: (MonadReader (env, proxy s, a) m, Reifies s (Getting a env a)) => m a
askE = do
    (e, s, _) <- ask
    return $ e ^. reflect s

data Foo = Foo { getFoo :: Int }

-- runFoo :: Monad n => Int -> (MonadEnv env Foo m => m a) -> n a
-- runFoo x m = do
--     e <- ask
--     reify (lens getter setter) $ \s ->
--         runReaderT m (e, s, Foo x)
--   where
--     getter (_, _, f) = getFoo f
--     setter (e, s, f) x = (e, s, f { getFoo = x })

-- useFoo :: MonadEnv env Foo m => m Int
-- useFoo = do
--     x <- askE
--     return x

data LogLevel = LevelDebug | LevelInfo | LevelWarn | LevelError | LevelOther Text
    deriving (Eq, Prelude.Show, Prelude.Read, Ord)

type LogSource = Text

type LogFunc = Loc -> LogSource -> LogLevel -> LogStr -> IO ()

class Monad m => MonadLogger m where
    monadLoggerLog :: Loc -> LogSource -> LogLevel -> LogStr -> m ()
instance (MonadIO m, MonadReader (env, Proxy s) m,
          Reifies s (Getting LogFunc env LogFunc))
         => MonadLogger m where
    monadLoggerLog a b c d = do
        (env, s) <- ask
        liftIO $ (env ^. reflect s) a b c d

myLogFunc :: Loc -> LogSource -> LogLevel -> LogStr -> IO ()
myLogFunc a b c (LS d) = putStrLn $ "Hello, world: " ++ d

defaultLoc :: Loc
defaultLoc = Loc "<unknown>" "<unknown>" "<unknown>" (0,0) (0,0)

logInfoN :: MonadLogger m => Text -> m ()
logInfoN =
    monadLoggerLog defaultLoc "" LevelInfo . toLogStr

bar :: MonadLogger m => m ()
bar = do
    logInfoN "This is a test"
    return ()

runLogger :: Reifies s (Getting LogFunc env LogFunc)
          => ReaderT (LogFunc, Proxy s) m a -> m a
runLogger m = reify id $ \s -> runReaderT m (myLogFunc, Proxy :: Proxy s)

main :: IO ()
main = runLogger bar
