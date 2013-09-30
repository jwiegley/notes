> archiveItem :: [Flag] -> FilePath -> IO ()
> archiveItem flags fp = do
>   if (Local `elem` flags)
>   then return ()
>   else invoke $ "mv " ++ escapePath fp ++ " " 
>                       ++ getEnv "HOME" ++ "/Archives/Inbox"
> 
>   if (Secure `elem` flags)
>   then invoke ("srm -mvf " ++ escapePath fp)
>   else removeItem fp
