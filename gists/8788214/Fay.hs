{-# LANGUAGE TupleSections #-}
module Runner.Handler.Fay
    ( runIdeCommand
    , runSohCommand
    ) where

import Data.Aeson (decodeStrict)
import Data.Aeson.Encode (fromValue)
import Data.Data (Data)
import ClassyPrelude.Yesod
import Runner.Import (Handler)
import Yesod.Fay
import Runner.Handler.Fay.Ide.Deployment
import Runner.Handler.Fay.Ide.Git
import Runner.Handler.Fay.Ide.Compilation
import Runner.Handler.Fay.Ide.File
import Runner.Handler.Fay.Ide.Info
import Runner.Handler.Fay.Ide.Messages
import Runner.Handler.Fay.Ide.Project
import Runner.Handler.Fay.Ide.Refactor
import Runner.Handler.Fay.TH
import Runner.Handler.Fay.Training
import Fay.Convert (showToFay, readFromFay)
import qualified Prelude
import FP.API
import FP.IsolationRunner.Types
import qualified Data.Text as T
import Data.Text.Lazy.Builder (toLazyText)

runIdeCommand :: Text -> Handler (Maybe Text)
runIdeCommand txt = do
    liftIO $ putStrLn $ "runIdeCommand 1.."
    runCommand $(fayDispatch ''IdeCommand) txt

runSohCommand :: Text -> RunnerBaseIO (Maybe Text)
runSohCommand = runCommand $(fayDispatch ''SohCommand)

runCommand :: (Show c, Data c, MonadLogger m, MonadIO m) => (c -> m (Maybe Text)) -> Text -> m (Maybe Text)
runCommand f (decodeStrict . encodeUtf8 -> Just (readFromFay -> Just cmd)) = do
    liftIO $ putStrLn $ "runCommand 1.."
    $logDebug $ tshow cmd
    liftIO $ putStrLn $ "runCommand 2: " ++ tshow cmd
    f cmd
runCommand _ txt = do
    liftIO $ putStrLn $ "runCommand 3: " ++ tshow txt
    return Nothing

render :: (Show a, MonadLogger m, Functor m) => Returns a -> a -> m (Maybe Text)
render r x = do
    $logDebug $ "Command Result: " <> tshow x
    result <- returnJson $ showToFay x
    -- What a mess!  Why doesn't Aeson provide such stuff?!
    return . Just . T.concat . toChunks . toLazyText $ fromValue result
