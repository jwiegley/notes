import Control.Monad.Morph
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Network (withSocketsDo)

type T m a = StateT Int m a

foo :: (MonadIO m, Show a) => T m a -> T m ()
foo x = do
  x' <- x
  modify (+1)
  v <- get
  liftIO $ putStrLn $ "x is " ++ show x' ++ " and v = " ++ show v

ugh :: IO a -> IO a
ugh k = do k; k

main :: IO ()
main = do
  x <- flip runStateT 0 $ do
    hoist ugh (foo (return "Hey"))
    liftIO $ print "Hello"
  print x
  return ()
