import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.Trans.State
import Control.Exception (throwIO, ArithException (..), Exception (..))
 
main = do
    eres <- flip runStateT () ((do
        -- throwM Overflow
        liftIO $ throwIO Overflow
	-- undefined
        return ()
        ) `finally` liftIO (putStrLn "finally!"))
    print eres
