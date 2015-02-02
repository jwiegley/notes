    shake shakeOptions { shakeVerbosity = Chatty } $ do
        want $ "hsc2hs.sh" : source : map (-<.> "cpp") plugins

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

        "hsc2hs.sh" *> \out -> liftIO $ do
            writeFile out hsc2hs_sh
            setFileMode out 0o755
