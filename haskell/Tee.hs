module Tee where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Loops
import qualified Data.Conduit as C
import           Data.Conduit.Internal
import qualified Data.Conduit.List as CL
import           Data.Void

main :: IO ()
main = do
    let printTee x    = liftIO $ putStrLn $ "tee " ++ show x
    let printNormal x = liftIO $ putStrLn $ "normal " ++ show x
    let ping          = liftIO $ putStrLn "ping"

    putStrLn "\n     -- Test 1 --"
    CL.sourceList [1..3::Int] C.=$= tee (CL.mapM_ printTee)
                              C.$$      (CL.mapM_ printNormal)

    putStrLn "\n     -- Test 2 --"
    CL.sourceList [1..3::Int] C.=$= tee (C.await >>= printTee)
                              C.$$      (CL.mapM_ printNormal)

    putStrLn "\n     -- Test 3 --"
    CL.sourceList [1..3::Int] C.=$= tee ((C.await >>= printTee) >> ping)
                              C.$$      (CL.mapM_ printNormal)

    putStrLn "\n     -- Test 4 --"
    CL.sourceList [1..3::Int] C.=$= tee ((C.await >>= printTee) >> ping >> (C.await >>= printTee))
                              C.$$      (CL.mapM_ printNormal)

    putStrLn "\n     -- Test 5 --"
    CL.sourceList [1..3::Int]
        C.=$= tee (do x <- C.await
                      printTee x
                      case x of Just y -> C.leftover y; Nothing -> return ()
                      x' <- C.await
                      printTee x'
                      case x' of Just y -> C.leftover y; Nothing -> return ())
        C.$$      (CL.mapM_ printNormal)



-- | Forks a stream, like the Unix `tee` utility.
--
-- This is like GNU tee, but yields each value first to the outer pipe, then
-- to the inner one.
tee :: Monad m => Sink a m () -> ConduitM a a m ()
tee (ConduitM sStart) = ConduitM $ go (injectLeftovers sStart)
  where
    go s = case s of
      -- The sink passed to tee cannot generate values.
      HaveOutput _ _ o -> absurd o

      -- Whenever a value is needed by the sink, we ask upstream and then
      -- yield the value to both the sink and downstream.  Note that if
      -- upstream terminates early, we pass the result value to the sink.
      NeedInput f lc   -> NeedInput (\i -> yield i >> go (f i)) (go . lc)

      -- Once the sink is Done, switch to being a transparent pass-through.
      Done ()          -> idP

      -- If an action must be executed to determined the next @Pipe@, do so
      -- and then process it with this function.
      PipeM mPipe      -> PipeM $ liftM go mPipe

      -- There can be no leftovers from the sink, since we called
      -- 'injectLeftovers' above.
      Leftover _ x    -> absurd x
