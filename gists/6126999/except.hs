import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Exception (throwIO, ArithException (..), Exception (..))
 
main = do
    eres <- runCatchT ((do
        -- throwM Overflow
        liftIO $ throwIO Overflow
	-- undefined
        CatchT $ return $ Left $ toException Underflow
        return ()
        ) `finally` liftIO (putStrLn "finally!"))
    print eres
