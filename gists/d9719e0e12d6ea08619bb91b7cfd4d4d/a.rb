{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=1000 #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Main where

import Categorical.NonDet
import Categorical.Gather
import ConCat.AltCat (ccc)
import ConCat.Category

main :: IO ()
main = case ccc @(NonDet ((->) :**: Gather)) (\() -> ()) of
    NonDet g ->
        print $ ccc @(->) (\(x :: p) -> let _ :**: Gather s = g x in s < 100) (error "p")
