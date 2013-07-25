wontWork :: Prelude.FilePath -> IO ()
wontWork path = do
    ls <- lines <$> readFile path
    let Just idx = findIndex (" Import " `isInfixOf`) ls
    writeFile path
        $ unlines
        $ take (idx + 2) ls
       ++ ["#import \"WS-Header.h\""]
       ++ drop (idx + 2) ls
