data ConflictType = BothModified
                  | ModifiedAndDeleted
                  | BothTypeChanged
                  | ModifiedAndTypeChanged
                  | DeletedAndTypeChanged

data ConflictEntry = ConflictEntry
    { conflictEntryType   :: ConflictType
    , conflictEntryLeft   :: Maybe TreeEntry
    , conflictEntryRight  :: Maybe TreeEntry
    , conflictEntryMerged :: Maybe TreeEntry
    }

data MergeResult m
    = MergeSuccess
    | MergeConflicted
        { mergeHead       :: CommitOid m
        , mergePulledHead :: CommitOid m
        , mergeCommit     :: CommitRef m
        , mergeConflicts  :: Map FilePath ConflictEntry
        }
