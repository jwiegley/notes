{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS -fno-warn-missing-signatures #-}

module Operational where

import                    ClassyPrelude.Conduit hiding (singleton)
import                    Control.Monad.Morph
import "free-operational" Control.Monad.Operational
import                    Control.Monad.Trans.Free
import                    Control.Monad.Trans.State (StateT)
import qualified          Control.Monad.Trans.State as State
import                    Data.Functor.Coyoneda
import qualified          Data.Map as M
import                    Data.Serialize
import                    Unsafe.Coerce

prog :: Program MyProgram ()
prog = do
    sayHello "Hello!"
    sayHello "Goodbye!"
    bindBool "Hello" (predicate True)
    bindBool "Goodbye" (predicate False)
    ifBool "Hello"
        (sayHello "Yes!")
        (sayHello "No!")
    ifBool "Goodbye"
        (sayHello "Yes!")
        (sayHello "No!")
    printBool (predicate True)
    printBool (predicate False)

{--------------------------------------------------------------------------}

data MyProgram a where
    SayHello  :: String -> MyProgram ()
    Predicate :: Bool -> MyProgram Bool
    BindBool  :: String -> Program MyProgram Bool -> MyProgram ()
    IfBool    :: String -> Program MyProgram () -> Program MyProgram ()
                 -> MyProgram ()
    PrintBool :: Program MyProgram Bool -> MyProgram ()

instance Serialize (Program MyProgram a) where
    put p = do
        _ <- interpretM eval (hoist (return . runIdentity) p)
        put (0 :: Int)
      where
        eval :: forall x. MyProgram x -> PutM x
        eval (SayHello x)    = put (1 :: Int) >> put x
        eval (Predicate x)   = put (2 :: Int) >> unsafeCoerce (put x)
        eval (BindBool x p') = put (3 :: Int) >> put x >> put p'
        eval (IfBool x t e)  = put (4 :: Int) >> put x >> put t >> put e
        eval (PrintBool p')  = put (5 :: Int) >> put p'

    get = go (return (unsafeCoerce ()))
      where
        go :: Program MyProgram a -> Get (Program MyProgram a)
        go x = do
            which <- get
            case which of
                (1 :: Int) -> do
                    y <- SayHello <$> get
                    go (x >> singleton (unsafeCoerce y))
                (2 :: Int) -> do
                    y <- Predicate <$> get
                    go (x >> singleton (unsafeCoerce y))
                (3 :: Int) -> do
                    y <- BindBool <$> get <*> get
                    go (x >> singleton (unsafeCoerce y))
                (4 :: Int) -> do
                    y <- IfBool <$> get <*> get <*> get
                    go (x >> singleton (unsafeCoerce y))
                (5 :: Int) -> do
                    y <- PrintBool <$> get
                    go (x >> singleton (unsafeCoerce y))
                _ -> return x

instance MFunctor (FreeT (Coyoneda MyProgram)) where
    hoist f (FreeT g) = FreeT (f (liftM (fmap (hoist f)) g))

instance MFunctor (ProgramT MyProgram) where
    hoist f (ProgramT g) = ProgramT (hoist f g)

sayHello  = singleton . SayHello
predicate = singleton . Predicate
bindBool  = (singleton .) . BindBool
ifBool    = ((singleton . ) .) . IfBool
printBool = singleton . PrintBool

main :: IO ()
main = case decode (encode prog) of
    Left e  -> error $ "Could not decode: " ++ e
    Right x -> do
        putStrLn "Direct evaluation in IO:"
        _ <- flip State.runStateT mempty $
            interpretM eval (hoist (return . runIdentity) prog)
        putStrLn "\nEvaluation after marshalling:"
        _ <- flip State.runStateT mempty $
            interpretM eval (hoist (return . runIdentity) x)
        return ()
  where
    eval :: (Functor m, MonadIO m)
         => MyProgram a -> StateT (Map String Bool) m a

    eval (SayHello x)   = liftIO $ print x

    eval (Predicate x)  = return x

    eval (BindBool n x) =
        interpretM eval (hoist (return . runIdentity) x)
            >>= \b -> State.modify (M.insert n b)

    eval (IfBool n t e) = do
        m <- State.get
        case M.lookup n m of
            Nothing -> error "Variable not set"
            Just b | b ->
                interpretM eval (hoist (return . runIdentity) t)
                   | otherwise ->
                interpretM eval (hoist (return . runIdentity) e)

    eval (PrintBool p) =
        interpretM eval (hoist (return . runIdentity) p)
            >>= \b -> liftIO $ print b
