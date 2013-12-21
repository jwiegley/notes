(>->) :: forall a b i o m. Monad m
      => ConduitM i a m () -> ConduitM a o m b -> ConduitM i o m b
u >-> d = u =$= d

runEffect :: forall m b. Monad m => ConduitM () Void m b -> m b
runEffect c = yield () $$ c

forC :: Monad m => Source m a -> (a -> m ()) -> m ()
forC p a = p $$ CL.mapM_ a

main :: IO ()
main = do
    runEffect $ forC (yield (1 :: Int) >> yield 2) $ liftIO . print

    runResourceT $ runEffect $
        sourceFile "/Volumes/Data/Home/Dropbox/Notes/conduitPrelude.hs"
            >-> CL.isolate 10
            >-> CT.decode CT.utf8
            >-> CT.lines
            >-> CL.mapM_ (liftIO . print)
