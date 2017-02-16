{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
import Control.Lens
import Control.Applicative

data Interval a = Interval { _intervalStart, _intervalEnd :: a }
  deriving (Read, Show, Eq, Ord)

data IntervalIndex = Start | End
  deriving (Read, Show, Eq, Ord)

-- Not the best name, sure
intervaled :: IndexedTraversal IntervalIndex (Interval a) (Interval b) a b
intervaled p (Interval start end) = Interval <$> indexed p Start start <*> indexed p End end

demo lo hi
     = [(0, Interval 0 10)]
     & traverse . _2 . intervaled
     %@~ \case Start -> min lo
               End   -> max hi
