module Main where

import Control.Monad
import Control.Monad.Trans.Cont

forBreakM ys x f =
    flip runContT (const (return x)) $ callCC $ \exit ->
        mapM_ (f exit) ys

main = do
    y <- forBreakM [1,2,3] True $ \exit x ->
        when (x == 2) $ exit False
    print y
