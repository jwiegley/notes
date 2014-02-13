-- If the new target's module is Main, it is always included
-- in compilation (whether ambiguous or not).
pfFiles.ix path.pfiAutoExcluded .= False

-- jww (2014-01-23): Here's what the above line of code looks
-- like without lens!
RWS.modify $ \files -> files
    { _pfFiles = M.adjust
        (\pfi -> pfi { _pfiAutoExcluded = False })
        path (_pfFiles files)
    }
