{-# LANGUAGE ScopedTypeVariables #-}

module DefPact where

import Control.Monad.Trans.State
import Control.Monad.Trans.Class

-- (defpact good:string (arg:string)
--   (step arg)
--   (step (+ "hello " arg))
--   (step arg)
-- )

data PactState = PactState {
    executed :: Bool
  , pactId   :: String
  , stepIdx  :: Int
  , yield    :: Bool
  }
  deriving (Show)

data Step m a = Step {
    stepId :: Int
  , runStep :: m a
  }

instance Show (Step m a) where
  show (Step i _) = "Step " ++ show i

type PactDef m a = State (Int, [Step m a]) ()

data Pact m a = Pact {
    pactState      :: PactState
  , remainingSteps :: [Step m a]
  }
  deriving (Show)

step :: Monad m => m a -> PactDef m a
step action = do
  (cur, steps) <- get
  put (succ cur, steps ++ [Step cur action])

compile :: PactDef m a -> Pact m a
compile pact = Pact {
    pactState = PactState False "" 0 False
  , remainingSteps = snd (execState pact (0, []))
  }

runPact :: Monad m => Pact m a -> StateT (Pact m a) m b -> m b
runPact = flip evalStateT

continuePact :: Monad m => StateT (Pact m a) m a
continuePact = do
  pact <- get
  case remainingSteps pact of
    [] -> error "Pact has completed"
    Step n action:xs -> do
      res <- lift $ action
      put $ Pact {
          pactState = (pactState pact) { executed = null xs, stepIdx = succ n }
        , remainingSteps = xs
        }
      pure res

good :: Monad m => String -> PactDef m String
good arg = do
  step $ pure "hello1"
  step $ pure $ "hello2 " ++ arg
  step $ pure "hello3"

main :: IO ()
main = do
  let pact = compile (good "john")
  runPact pact $ do
    res1 <- continuePact
    lift $ print res1
    res2 <- continuePact
    lift $ print res2
    res3 <- continuePact
    lift $ print res3
