        let toFay (k, (lv, rv)) =
                SharedTypes.Ide.MergeFile
                    (repack k)
                    (SharedTypes.All.MergeModifyPair
                     ((toMergeModifyKind lv), (toMergeModifyKind rv)))
            fayVals = map toFay $ unpack mergeConflicts
        forM_ fayVals $ \(SharedTypes.Ide.MergeFile k pair) -> do
            updateWhere
                [ModuleProject ==. pid, ModuleGitPath ==. Just (repack k)]
                [ModuleMergeStatus =. Just pair]
            updateWhere
                [DataFileProject ==. pid, DataFileName ==. DataFileNameCon k]
                [DataFileMergeStatus =. Just pair]
        return $ Right $ GPRManualMerge
            (FayManualMergeId mergeCommit)
            (MergeFiles fayVals)
