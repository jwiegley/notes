-- | A Job is basically a type-wrapper around a constrained monadic action, so
--   that we can distinguish between different jobs with the same basic type
--   at the type level.
class Job t m a b where
    type Env m :: Constraint
    action :: Env m => t -> a -> m b

data ChrisJob m = ChrisJob (Int -> m Int)

instance MonadIO m => Job (ChrisJob m) m Int Int where
    type Env m = MonadIO m
    action (ChrisJob f) x = f x
