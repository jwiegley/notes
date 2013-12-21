main :: IO ()
main = do
  GHC.Conc.setNumCapabilities 2 -- use 2 cores; must link with -threaded

  opts <- cmdArgs gitAll        -- process command-line options
  forM_ (dirs opts) $ \dir -> do
    c <- newChan
    forkIO $ findDirectories c ".git" dir

    cs <- getChanContents c
    mapM_ (\x -> x >>= processDirectory) cs

processDirectory :: FilePath -> IO ()
processDirectory dir = do
  putStrLn dir

findDirectories :: Chan (Maybe FilePath) -> String -> FilePath -> IO ()
findDirectories c name dir = do
  dirs <- search name dir
  mapM_ (writeChan c . Just) dirs
  writeChan c Nothing

search :: FilePath -> FilePath -> IO [FilePath]
search name dir =
  F.find F.always (F.fileName F.==? name) dir
