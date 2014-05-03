guessLocal = do
    ghc <- findExecutable "ghc"
    home <- getHomeDirectory
    lib <- getLibDir
    path <- lookupEnv "HOOGLE_DOC_PATH"
    let xs = [takeDirectory (takeDirectory lib) </> "doc" {- Windows, installed with Cabal -}  ] ++
             [takeDirectory (takeDirectory ghc) </> "doc/html/libraries" | Just ghc <- [ghc] {- Windows, installed by GHC -} ] ++
             maybeToList path ++
             [home </> ".cabal/share/doc/x86_64-osx-ghc-7.6.3" {- Linux -} ] ++
             [home </> ".cabal/share/doc" {- Linux -} ]
    filterM doesDirectoryExist xs
