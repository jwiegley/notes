-- | Convert a 'Control.Foldl.FoldM' fold abstraction into a Sink.
--
--   NOTE: This requires ImpredicativeTypes in the code that uses it.
--
-- >>> fromFoldM (FoldM ((return .) . (+)) (return 0) return) $ yieldMany [1..10]
-- 55
fromFoldM :: Monad m => FoldM m a b -> Sink a m b
fromFoldM (FoldM step initial final) src =
    initial >>= (\r -> sink r ((lift .) . step) src) >>= final
{-# INLINE fromFoldM #-}

-- | Convert a Sink into a 'Control.Foldl.FoldM', passing it as a continuation
--   over the elements.
--
-- >>> toFoldM sumC (\f -> Control.Foldl.foldM f [1..10])
-- 55
toFoldM :: Monad m => Sink a m b -> (forall r. FoldM m a r -> m r) -> m b
toFoldM s f = s $ source $ \k yield ->
    EitherT $ liftM Right $ f $
        FoldM (\r x -> either id id `liftM` runEitherT (yield r x))
            (return k) return
{-# INLINE toFoldM #-}
