forall e m. Nix.MonadNix e m
                   => (V.NValue m -> m ()) -> V.NValue m -> m ()
            result h = case attr opts of
                Nothing -> h
                Just (Text.splitOn "." -> keys) -> go keys
              where
                go :: [Text.Text] -> V.NValue m -> m ()
                go [] v = h v
                go ((Text.decimal -> Right (n,"")):ks) v = case v of
                    V.NVList xs -> case ks of
                        [] -> T.force @(V.NValue m) @(V.NThunk m) (xs !! n) h
                        _  -> T.force (xs !! n) (go ks)
                    _ -> errorWithoutStackTrace $
                            "Expected a list for selector '" ++ show n
                                ++ "', but got: " ++ show v
                go (k:ks) v = case v of
                    V.NVSet xs _ -> case M.lookup k xs of
                        Nothing ->
                            errorWithoutStackTrace $
                                "Set does not contain key '"
                                    ++ Text.unpack k ++ "'"
                        Just v' -> case ks of
                            [] -> T.force v' h
                            _  -> T.force v' (go ks)
                    _ -> errorWithoutStackTrace $
                        "Expected a set for selector '" ++ Text.unpack k
                            ++ "', but got: " ++ show v

        if | evaluate opts, debug opts ->
                 runLazyM $ compute Nix.tracingEvalLoc expr $
                     result (liftIO . print)

           | evaluate opts, not (null args) ->
                 runLazyM $ compute Nix.evalLoc expr $
                     result (liftIO . print)

           | evaluate opts -> 