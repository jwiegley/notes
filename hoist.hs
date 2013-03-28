import Control.Monad.Morph
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Network (withSocketsDo)

type T m a = StateT () m a

foo :: (MonadIO m, Show a) => T m a -> T m ()
foo x = do
    x' <- x
    liftIO $ putStrLn $ "x is " ++ show x'

main = do
    flip runStateT () $ do
        hoist withSocketsDo (foo (return "Hey"))
        liftIO $ print "Hello"
