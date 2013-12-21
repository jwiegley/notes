data ModificationKind = Unchanged | Modified | Added | Deleted | TypeChanged
                      deriving (Eq, Ord, Enum, Show)

data MergeStatus
    = NoConflict
    | BothModified
    | LeftModifiedRightDeleted
    | LeftDeletedRightModified
    | BothAdded
    | LeftModifiedRightTypeChanged
    | LeftTypeChangedRightModified
    | LeftDeletedRightTypeChanged
    | LeftTypeChangedRightDeleted
    | BothTypeChanged
    deriving (Eq, Ord, Enum, Show)

mergeStatus :: ModificationKind -> ModificationKind -> MergeStatus
mergeStatus Unchanged Unchanged     = NoConflict
mergeStatus Unchanged Modified      = NoConflict
mergeStatus Unchanged Added         = undefined
mergeStatus Unchanged Deleted       = NoConflict
mergeStatus Unchanged TypeChanged   = NoConflict

mergeStatus Modified Unchanged      = NoConflict
mergeStatus Modified Modified       = BothModified
mergeStatus Modified Added          = undefined
mergeStatus Modified Deleted        = LeftModifiedRightDeleted
mergeStatus Modified TypeChanged    = LeftModifiedRightTypeChanged

mergeStatus Added Unchanged         = undefined
mergeStatus Added Modified          = undefined
mergeStatus Added Added             = BothAdded
mergeStatus Added Deleted           = undefined
mergeStatus Added TypeChanged       = undefined

mergeStatus Deleted Unchanged       = NoConflict
mergeStatus Deleted Modified        = LeftDeletedRightModified
mergeStatus Deleted Added           = undefined
mergeStatus Deleted Deleted         = NoConflict
mergeStatus Deleted TypeChanged     = LeftDeletedRightTypeChanged

mergeStatus TypeChanged Unchanged   = NoConflict
mergeStatus TypeChanged Modified    = LeftTypeChangedRightModified
mergeStatus TypeChanged Added       = undefined
mergeStatus TypeChanged Deleted     = LeftTypeChangedRightDeleted
mergeStatus TypeChanged TypeChanged = BothTypeChanged

data MergeResult m
    = MergeSuccess
        { mergeCommit    :: CommitOid m
        }
    | MergeConflicted
        { mergeCommit    :: CommitOid m
        , mergeHeadLeft  :: CommitOid m
        , mergeHeadRight :: CommitOid m
        , mergeConflicts :: Map FilePath MergeStatus
        }
