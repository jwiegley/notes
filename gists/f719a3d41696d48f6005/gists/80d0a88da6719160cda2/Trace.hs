simplify :: Maybe String -> Bool -> IO ByteString -> IO ()
simplify mapFile stats origTrace = do
  pointers <- parseMap mapFile
  fileSource <- origTrace
  let normalizedTrace = normalize' pointers fileSource
      action =
          mapM_ simplifyStep $ zip [1..] $ filterAuthorities (normalizedTrace)
  if stats
      then do
          action
          putStrLn $ showStatistics (generateStatistics normalizedTrace)
      else action
  where
    filterAuthorities = filter (\step -> not (stepAuthority step `elem` nameAuths))
    nameAuths = map (Name) auths
    auths = ["Processor_Authority"] -- TODO : eventually parameterize
