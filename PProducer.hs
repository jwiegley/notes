{-# LANGUAGE RecordWildCards #-}

module PProducer where

import Control.Monad.Trans.State
import Pipes as P
import Pipes.Prelude as P

data PipeState m a = PipeState
    { psLeftover  :: Maybe a
    , psFinalizer :: m ()
    , psExhausted :: Bool
    }

type PProducer a m b = StateT (PipeState m a) (P.Producer a m) b

liftProducer :: Monad m => P.Producer a m b -> PProducer a m b
liftProducer p = StateT $ flip go p
  where
    go ps@(PipeState {..}) p' =
        case psLeftover of
            Nothing -> do
                eres <- lift $ next p'
                case eres of
                    Left b -> do
                        lift psFinalizer
                        return (b, ps { psExhausted = True })
                    Right (a, rest) -> do
                        P.yield a
                        go ps rest
            Just l -> do
                P.yield l
                go ps p'

main :: IO ()
main = do
    runEffect $
        P.stdinLn >-> P.take 10 >-> P.stdoutLn
    runEffect $
        evalStateT
            (liftProducer P.stdinLn)
            (PipeState Nothing (putStrLn "Hello!") False)
            >-> P.take 10
            >-> P.stdoutLn
