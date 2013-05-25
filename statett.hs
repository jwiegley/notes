import Control.Monad.Layer
import Control.Monad.Interface.Try
import Control.Monad.Interface.State
import Control.Monad.Trans.State (runStateT)
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad (mzero)

bar :: Bool -> IO (Maybe (), Int)
bar sw = flip runStateT 0 $ runMaybeT $ bracket
    (do
        lift $ putStrLn "init"
        modify (+1))
    (\() -> do
        modify (+16)
        lift $ putStrLn "close"
        modify (+32)
        mzero
        modify (+64))
    (\() -> do
        modify (+2)
        lift $ putStrLn "body"
        modify (+4)
        if sw then mzero else error "oops"
        modify (+8))

main = do
    bar True >>= print
    bar False >>= print
