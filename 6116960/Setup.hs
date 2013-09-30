{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Applicative hiding ((*>))
import Control.Exception
import Control.Monad
import Data.List (find, findIndex, isInfixOf)
import Data.Maybe (isJust)
import Development.Shake hiding (doesDirectoryExist)
import Development.Shake.FilePath hiding (exe)
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Program
import Distribution.Simple.Setup
import Prelude hiding (FilePath)
import System.Directory

data Lens a b = Lens (b->a) (a->b -> b)
infixr 9 #

(#) :: Lens a b -> Lens b c -> Lens a c
(#) (Lens getA setA) (Lens getB setB) =
    Lens (getA . getB) (\a c -> setB (setA a $ getB c) c)

get :: Lens a b -> b -> a
get (Lens lensGet _) b = lensGet b

set :: Lens a b -> a -> b -> b
set (Lens _ lensSet) a b = lensSet a b

main :: IO ()
main = do
    let hooks = simpleUserHooks
    defaultMainWithHooks $
#if darwin_HOST_OS
        set lensBuildHook2UserHooks (myBuildHook hooks)
#endif
            hooks
                { buildHook = \a b c d ->
                    buildClientLibrary a b c d
                        >>= \x -> buildHook simpleUserHooks x b c d
                }
  where
    oldbuildhook hooks = get lensBuildHook2UserHooks hooks

    myBuildHook hooks packDesc locBuildInfo =
        oldbuildhook hooks packDesc
            (set lensProgramConfig2LocBuildInfo newProgramConfig locBuildInfo)
      where
        !(Just !oldGhcConf) = lookupProgram ghcProgram oldProgramConfig
        oldProgramConfig = get lensProgramConfig2LocBuildInfo locBuildInfo
        oldOverrideArgs =
            get lensProgramOverrideArgs2ConfiguredProgram oldGhcConf
        newOverrideArgs = oldOverrideArgs ++ ["-pgma clang++", "-pgmc clang++"]
        newGhcConf =
            set lensProgramOverrideArgs2ConfiguredProgram newOverrideArgs
                oldGhcConf
        newProgramConfig = updateProgram newGhcConf oldProgramConfig

buildClientLibrary :: PackageDescription
                   -> LocalBuildInfo
                   -> UserHooks
                   -> BuildFlags
                   -> IO PackageDescription
buildClientLibrary pdesc _binfo _userHooks _bflags = do
    let cybsDirBase = "dist/build/libcybs"
    createDirectoryIfMissing True cybsDirBase
    cybsDir <- canonicalizePath cybsDirBase
    cwd <- getCurrentDirectory
    (do setCurrentDirectory cybsDir
        darwin <- doesDirectoryExist "/usr/local/opt/gsoap"
        make (cwd </> "FP/Merchant/Processor") darwin
        return pdesc)
        `finally` setCurrentDirectory cwd

make :: FilePath -> Bool -> IO ()
make dir darwin = do
    let source   = "CybsSoapClient.cpp"
        plugins  = [ "wsseapi.c"
                   , "wsaapi.c"
                   , "smdevp.c"
                   , "mecevp.c"
                   ]
        gSOAP    = "soapcpp2"
        gWsdl    = "wsdl2h"
        soapH    = gSOAPDir </> "include/stdsoap2.h"
        gSOAPDir = if darwin
                   then "/usr/local/opt/gsoap"
                   else "/usr"
        gSOAPPluginDir = gSOAPDir </> "share/gsoap/plugin"

    shake shakeOptions { shakeVerbosity = Chatty } $ do
        want $ source : map (-<.> "cpp") plugins

        map (-<.> "cpp") plugins *>> \outs -> do
            need $ map (gSOAPPluginDir </>) plugins
                ++ ["cybersource.h", soapH]
            forM_ outs $ \out ->
                command_ [] "cp"
                    [ "-p"
                    , gSOAPPluginDir </> (out -<.> "c")
                    , out -<.> "cpp"
                    ]

        source *> \out -> do
            need $ [dir </> source, "cybersource.h", soapH]
            command_ [] "cp"
                [ "-p"
                , dir </> (out -<.> "cpp")
                , out
                ]

        "cybersource.h" *> \out -> do
            let typemap = gSOAPDir </> "share/gsoap/WS/WS-typemap.dat"
            need $ [typemap] ++ map (dir </>)
                [ "CyberSourceTransaction.wsdl"
                , "CyberSourceTransaction.xsd"
                ]
            command_ [] gWsdl
                [ "-t"
                , typemap
                , "-s"
                , "-o"
                , out
                , "-I" ++ dir
                , dir </> "CyberSourceTransaction.wsdl"
                ]
            liftIO $ patchCybersourceH out

            let importDir = gSOAPDir </> "share/gsoap/import"
            command_ [] gSOAP ["-j", "-C", "-I" ++ importDir, out]
            command_ [] gSOAP ["-C", "-I" ++ importDir, out]

patchCybersourceH :: FilePath -> IO ()
patchCybersourceH path = do
    ls <- lines <$> readFile path
    void $ evaluate (length ls) -- force the whole file to be read in
    unless (isJust (find ("WS-Header" `isInfixOf`) ls)) $ do
        let Just idx = findIndex (" Import " `isInfixOf`) ls
        writeFile path
            $ unlines
            $ take (idx + 3) ls
           ++ ["#import \"WS-Header.h\""]
           ++ drop (idx + 3) ls

lensProgramOverrideArgs2ConfiguredProgram :: Lens [String] ConfiguredProgram
lensProgramOverrideArgs2ConfiguredProgram =
    Lens (\ConfiguredProgram{programOverrideArgs}-> programOverrideArgs)
        (\newargs confprog -> confprog{programOverrideArgs = newargs})

lensBuildHook2UserHooks
    :: Lens (PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags
             -> IO ()) UserHooks
lensBuildHook2UserHooks =
    Lens (\UserHooks{buildHook}->buildHook) (\ bh  uhook -> uhook{buildHook=bh})

lensProgramConfig2LocBuildInfo :: Lens (ProgramConfiguration) (LocalBuildInfo)
lensProgramConfig2LocBuildInfo =
    Lens (\LocalBuildInfo{withPrograms}-> withPrograms)
        (\wprog lbi -> lbi{withPrograms= wprog})
