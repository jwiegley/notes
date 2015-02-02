-- | A Git commit SHA in textual form.
newtype CommitSHA = CommitSHA { unCommitSHA :: Text }
    deriving (Eq, Read, Show, Data, Typeable
#ifndef FAY
             , Ord, Serialize, Generic, Hashable
             , ToJSON, FromJSON, PathPiece
#endif
             )

-- | A Git branch name, such as "master", or "merge/master".
newtype BranchName = BranchName { unBranchName :: Text }
    deriving (Eq, Read, Show, Data, Typeable
#ifndef FAY
             , Ord, Serialize, Generic, Hashable
             , ToJSON, FromJSON, PathPiece
#endif
             )

-- | A Git ref name, such as "refs/heads/master".
newtype RefName = RefName { unRefName :: Text }
    deriving (Eq, Read, Show, Data, Typeable
#ifndef FAY
             , Ord, Serialize, Generic, Hashable
             , ToJSON, FromJSON, PathPiece
#endif
             )

#ifndef FAY
branchToRef :: BranchName -> RefName
branchToRef (BranchName name) = RefName ("refs/heads/" <> name)

refToBranch :: RefName -> BranchName
refToBranch (RefName name) =
    BranchName (T.reverse . T.takeWhile (/='/') . T.reverse $ name)

mergeBranch :: BranchName -> BranchName
mergeBranch b@(BranchName name)
    | "merge/" `T.isPrefixOf` name = b
    | otherwise = BranchName ("merge/" <> name)

mergeRef :: RefName -> RefName
mergeRef = branchToRef . mergeBranch . refToBranch
#endif

-- | A reference to a specific commit, which can be done by several different
--   means.
data CommitName = CommitByBranch BranchName
                | CommitByRef RefName
                | CommitBySHA CommitSHA
    deriving (Eq, Read, Show, Data, Typeable
#ifndef FAY
             , Ord, Generic
#endif
             )

#ifndef FAY
instance Serialize CommitName
instance Hashable CommitName
instance ToJSON CommitName
instance FromJSON CommitName

commitNameToBranch :: CommitName -> Maybe BranchName
commitNameToBranch (CommitByBranch b) = Just b
commitNameToBranch (CommitByRef r)    = Just (refToBranch r)
commitNameToBranch _                  = Nothing

commitNameToRef :: CommitName -> Maybe RefName
commitNameToRef (CommitByBranch b) = Just (branchToRef b)
commitNameToRef (CommitByRef r)    = Just r
commitNameToRef _                  = Nothing
#endif
