{-# LANGUAGE NamedFieldPuns #-}

import Control.Exception.Base
import Control.Monad
import Distribution.PackageDescription (PackageDescription(..))
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo (LocalBuildInfo(..), InstallDirs(..),
                                           absoluteInstallDirs)
import Distribution.Simple.Program.Types
import Distribution.Simple.Setup
import Distribution.Simple.Utils
import System.Directory

main = defaultMainWithHooks simpleUserHooks
    { preConf = \a b -> makeLib a b >> preConf simpleUserHooks a b
    , postInst = myPostInst }

cabalInstallProgram :: Program
cabalInstallProgram = (simpleProgram "cabal") {
    programFindVersion = findProgramVersion "--numeric-version" id
  }

makeLib :: Args -> ConfigFlags -> IO ()
makeLib _ flags = do
  cwd <- getCurrentDirectory
  finally
    (do createDirectoryIfMissing True "dist/build/libgit2"
        setCurrentDirectory "dist/build/libgit2"
        rawSystemExit (fromFlag $ configVerbosity flags) "env"
          [ "cmake"
          , "-DBUILD_SHARED_LIBS=OFF"
          , "-DTHREADSAFE=ON"
          , "../../../libgit2" ]
        rawSystemExit (fromFlag $ configVerbosity flags) "env"
          ["cmake", "--build", "."])
    (setCurrentDirectory cwd)

type PostInstHook = Args -> InstallFlags -> PackageDescription
                    -> LocalBuildInfo -> IO ()

myPostInst :: Args -> InstallFlags -> PackageDescription -> LocalBuildInfo
              -> IO ()
myPostInst _ (InstallFlags { installVerbosity }) pkg lbi = do
  print $ "libdir: " ++ libdir (absoluteInstallDirs pkg lbi NoCopyDest)
  -- cwd <- getCurrentDirectory
  -- finally
  --   (do setCurrentDirectory "dist/build/libgit2"
  --       -- rawSystemExit (fromFlag installVerbosity) "env"
  --       --   [ "cmake"
  --       --   , "-DCMAKE_INSTALL_PREFIX="
  --       --     ++ prefix (absoluteInstallDirs pkg lbi NoCopyDest)
  --       --   , "../../../libgit2" ]
  --       rawSystemExit (fromFlag installVerbosity) "env"
  --         [ "cmake", "--build", ".", "--target", "install" ])
  --   (setCurrentDirectory cwd)

-- Setup.hs ends here