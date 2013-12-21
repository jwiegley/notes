main :: IO ()
main = do
  -- use 2 cores; this utility must be linked with -threaded, otherwise
  -- everything will happen sequentially
  GHC.Conc.setNumCapabilities 2

  -- process command-line options
  opts <- cmdArgs gitAll

  -- Do a find in all directories (in sequence) in a separate thread, so that
  -- the list of directories is accumulated while we work on them
  c <- newChan
  forkIO $ findDirectories c ".git" (dirs opts)
  mapDirectories c processDirectory

  where mapDirectories c f = do
          elem <- readChan c
          case elem of
            Nothing -> return ()
            Just x  -> do
              f x
              mapDirectories c f

processDirectory :: FilePath -> IO ()
processDirectory dir = do
  putStrLn dir

-- Helper functions

findDirectories :: Chan (Maybe FilePath) -> String -> [FilePath] -> IO ()
findDirectories c name dirs =
  forM_ dirs $ findDirectories' c name
  where findDirectories' c name dir = do
          xs <- search name dir
          mapM_ (writeChan c . Just) xs
          writeChan c Nothing

search :: FilePath -> FilePath -> IO [FilePath]
search name dir =
  F.find F.always (F.fileName F.==? name) dir
