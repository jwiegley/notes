data ModificationKind = Unchanged | Modified | Added | Deleted
                      deriving (Eq, Ord, Enum, Show)

data MergeResult m
    = MergeSuccess
        { mergeCommit    :: CommitOid m
        }
    | MergeConflicted
        { mergeCommit    :: CommitOid m
        , mergeHeadLeft  :: CommitOid m
        , mergeHeadRight :: CommitOid m
        , mergeConflicts :: Map FilePath (ModificationKind, ModificationKind)
        }
