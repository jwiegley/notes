#!/usr/bin/env runhaskell

module Archiver where

{- Archiver, version 1.0

   by John Wiegley <johnw@newartisans.com>

   Usage: archive [OPTION...] <FILE | DIRECTORY>...

   Archives a file or directory by compressing it (if need be) and moving it
   to my ~/Archives/Inbox folder.

   Several thing happen during the course of this operation:

    1. If the file has the exention ".dmg", then it will be converted to a
       disk image with bzip2 internal compression, using hdiutil.

    2. If the file is already compressed by another means, it won't be
       compressed further.

    3. If compression occurred, and the compressed name is different from the
       original, the original is deleted.  NOTE: If the -s flag was given the
       original is securely deleted.

    4. If the -l flag is given, the file is not moved.

    5. After all is done, and the file (possibly) moved, it will have its SHA1
       checksum saved as an extended attribute. -}

import Data.List
import Data.IORef
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.FilePath.Posix
import System.Posix.Process
import Control.Monad
import Control.Monad.State
import Control.Monad.Error
import Control.Monad.Trans
import Control.Exception
import HSH
import HSH.ShellEquivs

{- Options supported by this script:

   `-l` causes the destination archive not to be moved into ~/Archives/Inbox.

   `-s` causes the original file (if different from the final archive name) to
   be securely removed. -}

data Flag = Local | Secure | Image deriving (Eq, Show)

options :: [OptDescr Flag]
options = [ Option ['l'] ["local"] (NoArg Local)  "Don't move archive file"
          , Option ['s'] ["secure"] (NoArg Secure) "Securely remove original"
          , Option ['i'] ["image"] (NoArg Image) "Place item in a .dmg image"
          ]

archiveOpts :: [String] -> IO ([Flag], [String])
archiveOpts argv =
    case getOpt Permute options argv of
             (o, n, []  ) -> return (o,n)
             (_, _, errs) -> ioError (userError (concat errs ++ usageInfo header options))
        where header = "Usage: archive [OPTION...] <FILE | DIRECTORY>..."

-- Apply the `archiveItem` function for every argument passed in.

data ScriptState = ScriptState { scriptFlags :: [Flag]
                               , tempPaths   :: [FilePath] }

type IOScript = ErrorT String (StateT ScriptState IO)

getScriptFlags :: IOScript [Flag]
getScriptFlags = get >>= \s -> return (scriptFlags s)

getTempPaths :: IOScript [FilePath]
getTempPaths = get >>= \s -> return (tempPaths s)

scriptFlagSet :: Flag -> IOScript Bool
scriptFlagSet f = do
  flags <- getScriptFlags
  return $ f `elem` flags

safeRunIO :: (ShellCommand a) => a -> IOScript ()
safeRunIO cmd = do
  result <- lift . lift . tryEC $ runIO cmd
  case result of
    Left ps  -> throwError $ "Command failed: " ++ show cmd ++ ": " ++ show ps
    Right () -> return ()

safeBracketCD :: FilePath -> IOScript a -> IOScript a
safeBracketCD fp action = do
  oldcwd <- lift . lift $ getCurrentDirectory
  lift . lift $ setCurrentDirectory fp
  action
  lift . lift $ setCurrentDirectory oldcwd

shell :: String -> [String] -> IOScript ()
shell cmd args = safeRunIO $ (cmd, args)

removeTempPaths :: IOScript ()
removeTempPaths = do
  flags <- getScriptFlags
  paths <- getTempPaths
  forM paths $ \fp ->
      if Secure `elem` flags
      then shell "srm" ["-mfr", fp]
      else shell "rm"  ["-fr", fp]
  return ()

main :: IOScript ()
main = do
  cmdArgs <- lift . lift $ getArgs
  (flags, args) <- lift . lift $ archiveOpts cmdArgs
  mapM archiveItem args
  removeTempPaths
  return ()

{- Archive an item by first compression it, resulting in two pathnames: The
   original item, and the result.  If not Local, move the result to
   ~/Archives/Inbox. Remove all temporaries and old files. -}

archiveItem :: FilePath -> IOScript ()
archiveItem fp = do
  nfp <- compressItem fp
  local <- scriptFlagSet Local
  if local
     then do
       finalDest <- safeMove nfp $ dirname fp </> basename nfp
       verifyFile finalDest
     else do
       (inbox:[]) <- lift . lift $ glob "~/Archives/Inbox"
       let dest = (inbox </> basename nfp)
       finalDest <- safeMove nfp dest
       verifyFile finalDest
  return ()

safeMove :: FilePath -> FilePath -> IOScript FilePath
safeMove src dst = do
  safeDest <- findUniqueName 0 dst
  lift . lift $ renameFile src safeDest
  return safeDest

findUniqueName :: Int -> FilePath -> IOScript FilePath
findUniqueName n fp = do
  let name = if n == 0
             then fp
             else dropExtension fp ++ "." ++ show n ++
                  takeExtension fp
  exists <- lift . lift $ doesFileExist name
  if exists
     then findUniqueName (n+1) fp
     else return name

compressItem :: FilePath -> IOScript FilePath
compressItem fp = do
  isdir <- lift . lift $ doesDirectoryExist fp
  exists <- lift . lift $ doesFileExist fp
  if not isdir && not exists
     then fail $ "Item does not exist: " ++ fp
     else do
       let ext  = takeExtension fp
           root = dropExtension fp
       image <- scriptFlagSet Image
       if image
          then makeDiskImage root fp
          else do
            if isdir
               then do
                 case ext of
                   ".app" -> makeDiskImage root fp
                   ".pkg" -> makeDiskImage root fp
                   _      -> compressDirectory fp
               else do
                 case ext of
                   ".7z"  -> return fp
                   ".gz"  -> recompressFile fp
                   ".bz2" -> recompressFile fp
                   ".zip" -> recompressZip fp
                   ".dmg" -> compressDiskImage fp
                   ".pkg" -> makeDiskImage root fp
                   _      -> compressFile fp

compressDirectory :: FilePath -> IOScript FilePath
compressDirectory fp = do
  let nfp = fp ++ ".tar.7z"
  bracketCD (dirname fp)
            (runIO $ ("tar", ["cf", "-", basename fp]) -|-
                     ("7za", ["a", nfp, "-si"]))
  return ([fp], nfp)
          
makeDiskImage :: FilePath -> FilePath -> IOScript FilePath
makeDiskImage root fp = do
  mkdir root 0o755
  shell "mv" [fp, root]
  let nfp = root ++ ".dmg"
  shell "hdiutil" ["create", "-srcfolder", root, nfp]
  (ofps, nfp2) <- compressDiskImage nfp
  return ((root:ofps), nfp2)

compressDiskImage :: FilePath -> IOScript FilePath
compressDiskImage fp = do
  tempPath <- getTemporaryDirectory
  let base = basename fp
      temp = tempPath </> base
  shell "hdiutil" ["convert", "-format", "UDBZ", "-o", temp, fp]
  return ([fp], temp)

compressFile :: FilePath -> IOScript FilePath
compressFile fp = do
  let nfp = fp ++ ".7z"
  bracketCD (dirname fp) $ shell "7za" ["a", nfp, basename fp]
  return ([fp], nfp)

recompressFile :: FilePath -> IOScript FilePath
recompressFile fp = do
  (ofps, ifp)  <- uncompressFile fp
  (ofps2, nfp) <- compressFile ifp
  return (ofps ++ ofps2, nfp)

uncompressFile :: FilePath -> IOScript FilePath
uncompressFile fp = do
  let ext = takeExtension fp
  case ext of
    ".gz"  -> (shell "gzip" ["-d", fp]  >> return ([], dropExtension fp))
    ".bz2" -> (shell "bzip2" ["-d", fp] >> return ([], dropExtension fp))
    _      -> fail $ "Unknown file extension: " ++ ext

recompressZip :: FilePath -> IOScript FilePath
recompressZip fp = do
  tempPath <- lift . lift $ getTemporaryDirectory
  let base = (dropExtension . basename) fp
      temp = tempPath </> base
  shell "unzip" ["-d", temp, fp]
  allFiles <- lift . lift $ getDirectoryContents temp
  let files = allFiles \\ [".", ".."]
  (ofps, nfp) <- case length files of
                   0 -> return ([], fp)
                   1 -> compressItem $ temp </> head files
                   _ -> compressDirectory temp
  return ((fp:temp:ofps), nfp)

verifyFile :: FilePath -> IOScript ()
verifyFile fp = shell "verify" ["-s", fp]
