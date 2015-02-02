newtype SequenceM m a = SequenceM (m a);

instance (Monad m, Monoid a) => Monoid (SequenceM m a) where {
  mempty = SequenceM (return mempty);
  SequenceM mx `mappend` SequenceM my = SequenceM (liftM2 mappend mx my);
}

whatever :: (MonadWriter (SequenceM IO ()) m) => m ();
whatever = tell (SequenceM (someIO :: IO ()));
