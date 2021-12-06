{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module SumLens where

import Control.Lens
import Data.Sum

projected :: e :< r => Prism' (Sum r v) (e v)
projected = prism' inject project

projectedC :: Const e :< r => Prism' (Sum r v) e
projectedC = prism' (inject . Const) (fmap getConst . project)