{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Journal.SumLens where

import Control.Lens
import Data.Sum

projected :: e :< r => Prism' (Sum r v) (e v)
projected = prism' inject project

projectedC :: Const e :< r => Prism' (Sum r v) e
projectedC = prism' (inject . Const) (fmap getConst . project)

liftTraversal :: (Const e :< r) => Traversal' e a -> Traversal' (Sum r v) a
liftTraversal tr f (project -> Just (Const e)) = inject . Const <$> tr f e
liftTraversal _ _ s = pure s
