{-# LANGUAGE NoImplicitPrelude #-}

module Update where

import ClassyPrelude.Conduit hiding (log)
import Control.Monad.RWS
import Git

data ProjectUpdate
    = SetProjectTarget
    | UpdateProjectFile TreeFilePath
    | RemoveProjectFile TreeFilePath
    deriving (Show, Eq)

data WorkingTreeUpdate = WorkingTreeUpdate
    deriving (Show, Eq)

data ProjectFileKind = Module | DataFile
    deriving (Show, Eq)

data ProjectFileInfo = ProjectFileInfo
    { pfiFileKind         :: ProjectFileKind
    , pfiModuleExcluded   :: Bool
    , pfiModuleHeaderName :: Maybe Text
    , pfiModuleStatus     :: ModuleStatus
    }
    deriving (Show, Eq)

data ProjectFiles
    = Map TreeFilePath ProjectFileInfo
    deriving (Show, Eq)

data ModuleStatus
    = UnknownStatus
    | WrongExtension
    | NotTextual
    | HeaderFilenameMismatch
    | ModuleOk
    deriving (Show, Eq, Read, Enum, Bounded, Ord)

data UpdateSource = UpdateSource Text | DeleteSource
    deriving (Show, Eq)
data UpdateData = UpdateData ByteString | DeleteData
    deriving (Show, Eq)

data UpdateContents
    = UCUpdateSource UpdateSource
    | UCUpdateData UpdateData
    deriving (Show, Eq)

data UpdateActions
    = UpdateIdeBackend TreeFilePath UpdateContents
    | UpdateModuleStatus TreeFilePath ModuleStatus
    deriving (Show, Eq)

-- | Give a 'ProjectUpdate' value, update the project.  The result of this
--   function is a set of updates to apply both to ide-backend and to the
--   local working tree mirror.
updateProject :: ProjectUpdate -> RWS () UpdateActions ProjectFiles ()
updateProject _ = undefined
