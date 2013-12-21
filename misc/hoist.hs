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
    liftIO $ putStrLn $ "x is " ++ show x'

main = do
    result <- flip runStateT 0 $ do
        hoist withSocketsDo (foo (return "Hey"))
        liftIO $ print "Hello"
    print result