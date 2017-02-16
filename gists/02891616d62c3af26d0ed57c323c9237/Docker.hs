{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module Shake.Docker where

import           Data.Foldable
import qualified Data.Text as T
import           Data.Traversable
import           Development.Shake
import           Development.Shake.Rule
import           Docker.Client

newtype ContainerQ = ContainerQ ContainerID
    deriving (Show, Eq)
newtype Modtime = Modtime Double
    deriving (Show, Eq)

instance Rule ContainerQ Modtime where
    storedValue _ (ContainerQ cid) = undefined
        -- exists <- System.Directory.doesFileExist x
        -- if exists then Just <$> getFileModtime x else return Nothing
    equalValue _ _ t1 t2 =
        if t1 == t2 then EqualCheap else NotEqual

-- Check for created containers (stopped or running)
(!%>) :: FilePattern -> (ContainerID -> Action ()) -> Rules ()
name !%> k = do
    cs <- runDockerT (defaultClientOpts, defaultHttpHandler) $ do
        eres <- listContainers defaultListOpts { Docker.Client.all = True }
        case eres of
            Left err -> error $ "Could not list containers: " ++ show err
            Right cs -> do
                cids <- map containerId
                     $ filter (any (\n -> name ?== T.unpack n) . containerNames)
                     $ cs
                forM cids $ \cid -> do
                    eres <- inspectContainer cid
                    case eres of
                        Left err -> error $ "Could not inspect containers: " ++ show err
                        Right details -> return (cid, state details)

    forM_ cs $ \(cid, st) ->
        rule (\(ContainerQ cid') ->
                  if cid == cid'
                  then Just (k cid)
                  else Nothing)
