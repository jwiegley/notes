readConfigFile initial file = handleNotExists $
  fmap (Just . parseConfig initial) (readFile file)
