type MapStore k v = Store k (Maybe v)

foo' :: Show v => MapStore String v -> IO ()
foo' st = do
  print $ extract st
  print $ extract (peeks (++"z") <<= peek "bar" <<= st)
  print $ peek "foo" st
  print $ peek "bar" st
  print $ peeks (++"z") st

bar' :: IO()
bar' = do
  foo' $ store (\k -> M.lookup k $ fromList [ ("foo",  "fooval")
                                            , ("fooz", "foozval")
                                            , ("bar",  "barval")
                                            , ("baz",  "bazval")
                                            , ("barz", "barzval") ])
               "baz"
